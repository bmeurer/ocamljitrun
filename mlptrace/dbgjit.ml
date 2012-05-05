(* file mlptrace/dbgjit.ml *)
(*** 
                                                                     
                           Objective Caml                           
                                                                    
      Basile Starynkevitch, projet Cristal, INRIA Rocquencourt      
                                                                    
  Copyright 2004 Institut National de Recherche en Informatique et  
  en Automatique.  All rights reserved.  This file is distributed   
  under the terms of the GNU Library General Public License, with   
  the special exception on linking described in file ../LICENSE.    
                                                                    
 ***)

let cvsid = "$Id: dbgjit.ml,v 1.9 2004-04-24 21:39:40 basile Exp $" ;;


module Ptrace = Dbgutil.PtraceX86;;


let num_of_file_descr (fd : Unix.file_descr) = ((Obj.magic fd): int);;

let string_of_file_descr fd = string_of_int (num_of_file_descr fd);;

let ocamljit_path = ref "../ocamljitrund";;
let guiscript_path = ref "./dbggui";;
let bytecode_path = ref "";;
let bytecode_input = ref "";;
let jitbatch = ref false;;
let jitasm = ref "";;

type jit_t = {
  jit_pid: int;
  jit_guispid: int;
  jit_interp_args: string list;
  jit_bytecode_args: string list;
  jit_bytecode_path: string;
  jit_interp_path: string;
  jit_outjit: out_channel;
  jit_outguis: out_channel;
  jit_symtable: (string,Nativeint.t) Hashtbl.t;
  jit_addrtable: (Nativeint.t,string) Hashtbl.t;
  jit_blocktable: (int,block_t) Hashtbl.t;
  jit_instrtable: (Nativeint.t, instr_t) Hashtbl.t; (*native addr to instr*)
  mutable jit_geninstrs: instr_t list;
  mutable jit_numgen: int;
  mutable jit_revision: string;
  mutable jit_ptracers: (jit_t -> unit) Queue.t;
  mutable jit_state: Nativeint.t;
}
and block_t = {
  bl_rank: int;
  bl_prog: Nativeint.t;
  bl_progsize: int;
  mutable bl_jpcref: Nativeint.t;
  mutable bl_instrs: instr_t list;
}
and instr_t = {
  ins_block: block_t; (*block*)
  ins_bytepc: Nativeint.t; (*bytecode addr*)
  ins_off: int; (*offset in block of bytecode*)
  ins_natad: Nativeint.t; (*native adress*)
  ins_txt: string; (*bytecode dissassembly*)
  ins_gen: int; (*generation number*)
}
;;

let add_jit_ptrace jit f = Queue.add f jit.jit_ptracers;;
let add_jit_breakpoint jit addr = 
  let addbr jit = ignore(Ptrace.patchcode jit.jit_pid addr (-1)) in
    add_jit_ptrace jit addbr;;

let block_jit jit n = Hashtbl.find jit.jit_blocktable n;;

(* first approximation of offsets in jit_state *)
let ref_offaccu = ref 0
and ref_offenv = ref 4
and ref_offxtrargs = ref 8
and ref_offbytepc = ref 12
and ref_offsavedbytepc = ref 32;;

let (==>) fmt sfun = (fun x -> Scanf.sscanf x fmt sfun);;

let parse_jit_to_debugger jit line = 
  let rec scanline = function
      [] -> Printf.eprintf "invalid jit to debugger line %S\n%!" line
    | s :: restscans -> 
	try 
	  s line
	with 
	    Scanf.Scan_failure _ -> scanline restscans
	  | ex -> Printf.eprintf "bad jit to debbuger line %S got %s\n%!" line (Printexc.to_string ex)
  in
  match line.[0] with
      '#' | '\n' | ' ' -> ()
    | 'B' -> scanline [ "BEGINGEN bl=%d gen=%d" 
			==> (fun blrk gencnt -> 
			       let bl = block_jit jit blrk in
				 jit.jit_geninstrs <- [];
				 jit.jit_numgen <- gencnt;
			) ]
    | 'E' -> scanline [ "ENDGEN bl=%d gen=%d"
			 ==> (fun blrk gencnt ->
			       let bl = block_jit jit blrk in
				 if jit.jit_numgen <> gencnt then 
				   Printf.eprintf "bad generation lin %S expected gen%d\n%!" 
				     line jit.jit_numgen;
				 let addins ins = 
				   if ins.ins_block <> bl || ins.ins_gen <> gencnt then
				     Printf.eprintf "instruction mess line %S insbytepc %nx %S\n%!"
				       line ins.ins_bytepc ins.ins_txt;
				   add_jit_breakpoint jit ins.ins_natad
				 in List.iter addins jit.jit_geninstrs;
				   jit.jit_geninstrs <- [];
				   jit.jit_numgen <- -1;
				   Printf.fprintf jit.jit_outjit "DIDGEN %d\n%!" gencnt;
				   flush jit.jit_outjit
			     ) ]
    | 'I' -> scanline [ "INSTR bl=%d off=%d bpc=%ni nad=%ni gen=%d txt=%S"
			 ==> (fun blrk off bpc nad gen txt ->
				let bl = block_jit jit blrk in
				let ins = {ins_block=bl; ins_bytepc=bpc; 
					   ins_off=off; ins_natad=nad; ins_gen=gen; 
					   ins_txt=txt} in
				  bl.bl_instrs <- ins:: bl.bl_instrs;
				  Hashtbl.add jit.jit_instrtable nad ins
			     ) ]
    | 'J' -> scanline [ "JITREVISION %S" ==> (fun id -> jit.jit_revision <- id) ;
		        "JITSTATE %ni" ==> (fun js -> jit.jit_state <- js)]
    | 'P' -> scanline [ "PROLOGBLOCK bl=%d jpc=%ni" 
			  ==> (fun rk jpcref ->
				 let bl = block_jit jit rk in
				   bl.bl_jpcref <- jpcref;
				   add_jit_breakpoint jit jpcref 
			      ) ]
    | 'M' -> scanline [ "MAKEBLOCK %d %ni %d" 
			  ==> (fun rk prog progsize ->
				 let bl = {bl_rank=rk; bl_prog=prog; bl_progsize=progsize; 
					   bl_jpcref= 0n; bl_instrs=[]
					  } in
				   Hashtbl.add jit.jit_blocktable rk bl
			      ) ]
    | 'S' -> scanline [ "STATEOFFSETS accu=%d env=%d xtra=%d bypc=%d savbpc=%d" 
			==> (fun oacc oenv oxtrag obytpc osavedbytpc ->
			       ref_offaccu := oacc; 
			       ref_offenv := oenv; 
			       ref_offxtrargs := oxtrag;
			       ref_offbytepc := obytpc; 
			       ref_offsavedbytepc := osavedbytpc) ]
			
    | _ -> Printf.eprintf "unexpected jit to debugger line %S\n%!" line
;;





let parse_guis_to_debugger jit line = 
  let rec scanline = function
      [] -> Printf.eprintf "invalid Guis to debugger line %S\n%!" line
    | s :: restscans -> 
	try 
	  s line
	with 
	    Scanf.Scan_failure _ -> scanline restscans
	  | ex -> Printf.eprintf "bad Guis to debbuger line %S got %s\n%!" line (Printexc.to_string ex)
  in
  match line.[0] with
      '#' | '\n' | ' ' -> ()
    | 'E' -> scanline [ "END%n" ==> (fun _ -> Unix.kill jit.jit_pid Sys.sigkill; exit 0)]
    | _ -> Printf.eprintf "unexpected Guis to debugger line %S\n%!" line
;;


let start_jit byteargsrev jitargsrev guisargsrev =
  let at_exit_kill pid = 
    let killit signum = try Unix.kill signum pid with Unix.Unix_error _ -> () in
  at_exit 
      (fun () -> 
	killit Sys.sigterm; 
	Dbgutil.fsleep 0.2; 
	killit Sys.sigkill) 
  in
  let jitsymtbl,jitadrtbl = Dbgutil.get_symbol_table !ocamljit_path in
  let devnull_fd = Unix.openfile  "/dev/null" [ Unix.O_RDONLY ] 0o400
  and from_guis_rdp, from_guis_wrp = Unix.pipe () 
  and to_guis_rdp, to_guis_wrp = Unix. pipe () in
  (* should start the guis with the reverse of guisargsrev *)
  let guis_pid = Unix.fork () in
  if guis_pid = 0 then begin
    (* child process - guis *)
    Unix.dup2 devnull_fd Unix.stdin;
    Unix.close to_guis_wrp;
    Unix.close from_guis_rdp;
    let guisargslist =  !guiscript_path 
      :: "-i" :: (string_of_file_descr to_guis_rdp)
      :: "-o" ::  (string_of_file_descr from_guis_wrp) 
      :: (List.rev guisargsrev) in
    Unix.execvp !guiscript_path (Array.of_list guisargslist) 
  end
  else begin
    Unix.close to_guis_rdp;
    Unix.close from_guis_wrp;
  end;
  at_exit_kill guis_pid;
  let from_jit_rdp, from_jit_wrp = Unix.pipe ()
  and to_jit_rdp, to_jit_wrp = Unix.pipe () in
  let jit_pid = Unix.fork () in
  if jit_pid = 0 then begin
    (* child process - jit interpreter *)
    if (String.length !bytecode_input) >0 then begin
      Unix.close Unix.stdin;
      let infd = Unix.openfile !bytecode_input [ Unix.O_RDONLY ] 0o400 in
      if infd <> Unix.stdin then begin
	Unix.dup2 infd Unix.stdin;
	Unix.close infd;
      end
    end
    else begin
      Unix.dup2 devnull_fd Unix.stdin;
      Unix.close devnull_fd 
    end;
    Unix.close from_jit_rdp;
    Unix.close to_jit_wrp;
    (* should build the OCAMLJTOPTION env. var *)
    let jitoptbuf = Buffer.create 80 in
    Buffer.add_string jitoptbuf "count";
    if !jitbatch then Buffer.add_string jitoptbuf ",batch";
    Printf.bprintf jitoptbuf ",todbgfd=%d,fromdbgfd=%d" 
      (num_of_file_descr  from_jit_wrp) (num_of_file_descr  to_jit_rdp);
    Unix.putenv "OCAMLJITOPTION" (Buffer.contents jitoptbuf);
    if String.length !jitasm>0 then Unix.putenv "OCAMLJITASM" !jitasm;
    Unix.execv !ocamljit_path 
      (Array.of_list 
	 (!ocamljit_path :: (List.rev jitargsrev) 
	  @ !bytecode_path :: (List.rev  byteargsrev)))
  end
  else begin
    (* parent process *)
    Unix.close from_jit_wrp;
    Unix.close to_jit_rdp;
  end;
  let outjit = Unix.out_channel_of_descr to_jit_wrp 
  and outguis = Unix.out_channel_of_descr to_guis_wrp 
  in
  at_exit_kill jit_pid;
  let jit = { jit_pid= jit_pid; 
	      jit_guispid= guis_pid; 
	      jit_interp_args= List.rev jitargsrev;
	      jit_bytecode_args= List.rev byteargsrev;
	      jit_bytecode_path= String.copy !bytecode_path;
	      jit_interp_path= String.copy !ocamljit_path;
	      jit_outjit= outjit;
	      jit_outguis= outguis;
	      jit_symtable= jitsymtbl;
	      jit_addrtable= jitadrtbl;
	      jit_blocktable= Hashtbl.create 311;
	      jit_instrtable= Hashtbl.create 3019;
	      jit_geninstrs= [];
	      jit_numgen= -1;
	      jit_revision= "";
	      jit_ptracers= Queue.create ();
	      jit_state= 0n
	    } in
  Printf.fprintf outguis 
    "start(%S,%S,%d)\n\n%!" 
    jit.jit_interp_path jit.jit_bytecode_path jit.jit_pid;
  Dbgutil.fsleep 0.1;
  jit
;;

let main () =
  let byteargs = ref []
  and jitargs = ref [] 
  and guisargs = ref [] in
  let addbytelist a = byteargs := a:: !byteargs in
  let addarg a = jitargs := a:: !jitargs in
    Arg.parse [
      "-i" , Arg.Set_string bytecode_input, "path = set path for std input of bytecode program (or /dev/null)";
      "-j" , Arg.Set_string ocamljit_path, "path = set path of jit interpreter - default is " ^ !ocamljit_path;
      "--jit_path", Arg.Set_string ocamljit_path, "path ## same as -j path";
      "-a", Arg.String addarg, "arg = add a single argument to jit interpreter";
      "--add-arg", Arg.String addarg, "arg ## same as -a arg";
      "-JB", Arg.Set jitbatch, "## jit in batch mode";
      "--jit-batch", Arg.Set jitbatch, "# same as -JB";
      "-JA", Arg.Set_string jitasm, "pathprefix = prefix for generated assembler code";
      "--jit-asm", Arg.Set_string jitasm, "pathprefix ##same as -JA pathprefix";
      "-A", Arg.String (fun a -> List.iter addarg (List.rev (Dbgutil.split_words a))), 
      "'args... ' ## add space-splitten arg to jit interpreter";
      "--split-args", Arg.String (fun a -> List.iter addarg (List.rev (Dbgutil.split_words a))), 
      "'args... ' ## same as -A 'args... '";
      "-b", Arg.Set_string bytecode_path, "path = set bytecode file - default is -b " ^ !bytecode_path;
      "--byte-code", Arg.Set_string bytecode_path, "path ## same as -b path ";
      "--guis-path", Arg.Set_string guiscript_path, "path = set GUIScript path - default: " ^ !guiscript_path;
      "-G", Arg.String (fun a -> guisargs := a :: !guisargs), 
      " arg ## add argument to GUIS script";
      "--add-guis-arg", Arg.String (fun a -> guisargs := a :: !guisargs), 
      " arg ## same as -G arg";
      "--", Arg.Rest addbytelist, "rest is passed to running bytecode";
    ] addbytelist
      "dbgjit -- a debugger for ocaml jit run";
    if (String.length !bytecode_path)==0 then 
      Printf.eprintf "dbgjit - missing bytecode path - use -b option\n%!";
    if String.contains !ocamljit_path '/' then  
      Unix.access !ocamljit_path  [Unix.X_OK];
    if String.contains !guiscript_path '/' then  
      Unix.access !guiscript_path  [Unix.X_OK];
    Unix.access !bytecode_path  [Unix.R_OK];
    if String.length !bytecode_input > 0 then
      Unix.access !bytecode_input [Unix.R_OK];
  let jit =  start_jit !byteargs !jitargs !guisargs in 
  ()
;;


try main ()
with 
  Unix.Unix_error(err,funam,arg) -> 
    Printf.eprintf "dbgjit failed with unix error - %s in %s on %S\n%!"
      (Unix.error_message err) funam arg
| ex -> 
    Printf.eprintf "dbgjit failed with %S\n%!" (Printexc.to_string ex); exit 2;;

(*** eof $Id: dbgjit.ml,v 1.9 2004-04-24 21:39:40 basile Exp $ **)
