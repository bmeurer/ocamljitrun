(* file mlptrace/dbgutil.ml *)
(*** 
                                                                     
                           Objective Caml                           
                                                                    
      Basile Starynkevitch, projet Cristal, INRIA Rocquencourt      
                                                                    
  Copyright 2004 Institut National de Recherche en Informatique et  
  en Automatique.  All rights reserved.  This file is distributed   
  under the terms of the GNU Library General Public License, with   
  the special exception on linking described in file ../LICENSE.    
                                                                    
 ***)

let cvsid = "$Id: dbgutil.ml,v 1.4 2004-04-24 21:40:03 basile Exp $";;

module PtraceX86 = struct
  type nativeint = Nativeint.t
  (** [peek pid adr] returns a word *)
  external peek : int -> nativeint -> nativeint = "mlptrace_peek"
  (** type of x86 integer register values *)
  type x86regs_t = {
      eip: nativeint;
      eax: nativeint;
      ebx: nativeint;
      ecx: nativeint;
      edx: nativeint;
      esi: nativeint;
      edi: nativeint;
      ebp: nativeint;
      esp: nativeint;
      eflags: nativeint;
      origeax: nativeint;
    }
  (** [peekregisters pid] return the registers value *)
  external peekregisters : int -> x86regs_t = "mlptrace_peekregisters"
  (** [patchcode pid adr byte] patch a byte of code - if byte<0 put a break *)
  external patchcode : int -> nativeint -> int -> int = "mlptrace_patchcode"
  (** [cont pid signum] do a PTRACE_CONT *)
  external cont: int -> int -> unit = "mlptrace_cont"
  (** [pread_kilobyte fd kiloadr] read from unix filedescr fd a kilobyte at kiloaddr<<10 *)
  external pread_kilobyte: Unix.file_descr -> int -> string = "mlptrace_pread_kilobyte"
end (*of PtraceX86*);;

(** split the words in a given string - giving a string list *)
let split_words ?(pos=0) str = 
  let slen = String.length str in
  let b = Buffer.create slen in
  let rec splitloop n rest =
    if (n>=slen) then 
      let w = Buffer.contents b in 
      if (String.length w)>0 then w::rest else rest
    else 
      let c = str.[n] in
      match c with 
	' ' | '\t' | '\r' | '\n' |  '\011' (*VT*) | '\012' (*FF*) -> 
	  let w = Buffer.contents b in 
	  Buffer.clear b; 
	  if (String.length w)>0 then 
	    splitloop (n+1) (w::rest)
	  else
	    splitloop (n+1) rest
      |	 _ -> Buffer.add_char b c; 
	  splitloop (n+1) rest
  in	  
  if (pos<0) then failwith "negative pos for split_words";
  List.rev (splitloop pos [])
;;

let get_symbol_table binam = 
  Unix.access  binam [ Unix.R_OK ];
  let nmcmd = Printf.sprintf "nm -g --defined-only %s" binam in
  let symhash = Hashtbl.create 2011 and adrhash = Hashtbl.create 2011 in
  let ch = Unix.open_process_in 
      nmcmd in
  let rec readloop () = 
    let add_symbol ad nam = 
      Hashtbl.add symhash nam ad;
      Hashtbl.add adrhash ad nam
    in
    let again = try 
      Scanf.fscanf ch "%nx %c %s " (fun ad tc nam -> add_symbol ad nam);
      true
    with End_of_file -> false
    in if again then readloop ()
  in readloop ();
  let st = Unix.close_process_in ch in
  match st with 
    Unix.WEXITED(0) -> symhash,adrhash
  | _ -> 
      Printf.eprintf "failed to get symbol table from %S\n%!" binam;
      failwith "get_symbol_table failed"
;;

type 'a loop_t = {
  lo_data: 'a;
  mutable lo_proc: 'a loop_proc_t list;
  mutable lo_input: 'a loop_input_t list;
  mutable lo_output: 'a loop_output_t list;
  mutable lo_delay: float;
}
and 'a loop_proc_t = { 
  lp_pid: int; 
  mutable lp_handler:  'a loop_t -> int * Unix.process_status -> unit }
and 'a loop_input_t = { 
  lr_fd: Unix.file_descr;  
  mutable lr_buf: string; 
  mutable lr_lastpos: int; 
  mutable lr_handler: 'a loop_t -> Unix.file_descr ->  string -> unit }
and 'a loop_output_t = {
  lw_fd: Unix.file_descr;
  mutable lw_writer: 'a loop_t -> Unix.file_descr -> unit }

let make_loop data = { lo_data=data; lo_proc=[]; lo_input=[]; lo_output=[]; lo_delay=0.5 };;

let loop_pids loop = List.map (fun {lp_pid=pid}->pid) loop.lo_proc;;
let loop_infds loop = List.map (fun {lr_fd=fd}->fd) loop.lo_input;;
let loop_outfds loop = List.map (fun {lw_fd=fd}->fd) loop.lo_output;;
let loop_delay loop = loop.lo_delay;;
let loop_data loop = loop.lo_data;;

let loop_add_input loop fd hdlr = 
  let rec findin = function
      [] -> 
	let lr = {lr_fd=fd; lr_buf=String.make 1024 '\000'; lr_lastpos=0; lr_handler=hdlr}  in
	loop.lo_input <- lr :: loop.lo_input 
    | lr :: rest -> 
	if lr.lr_fd = fd then lr.lr_handler <- hdlr 
	else findin rest
  in findin loop.lo_input;;

let loop_remove_input loop fd = 
  loop.lo_input <- List.filter (fun lr -> lr.lr_fd<>fd) loop.lo_input;;

let loop_add_output loop fd hdlr = 
  let rec findout = function
      [] -> 
	let lw = {lw_fd=fd; lw_writer=hdlr} in
	  loop.lo_output <- lw :: loop.lo_output
    | lw :: rest ->
	if lw.lw_fd = fd then lw.lw_writer <- hdlr 
	else findout rest
  in findout loop.lo_output;;

let loop_remove_output loop fd = 
  loop.lo_output <- List.filter (fun lw -> lw.lw_fd<>fd) loop.lo_output;;

let loop_add_process loop pid hdlr = 
  let rec findproc = function 
      [] -> let lp = {lp_pid=pid; lp_handler=hdlr} in
	loop.lo_proc <- lp :: loop.lo_proc
    | lp :: rest ->
	if lp.lp_pid = pid then lp.lp_handler <- hdlr
	else findproc rest
  in findproc loop.lo_proc;;

let loop_remove_process loop pid = 
  loop.lo_proc <- List.filter (fun lp -> lp.lp_pid<>pid) loop.lo_proc;;

let run_loop loop = 
  let rec pidloop = function
      [] -> false
    | lp::restlp ->
	let wpid,wstatus = Unix.waitpid [ Unix.WNOHANG ] lp.lp_pid in
	  if wpid = lp.lp_pid then begin
	    lp.lp_handler loop  (wpid,wstatus);
	    true
	  end else pidloop restlp
  in
  let io loop = 
    let infds = List.map (fun {lr_fd=fd}->fd) loop.lo_input 
    and outfds = List.map (fun {lw_fd=fd}->fd) loop.lo_output
    and readfd rfd = 
      let rec findli = function 
	  [] -> assert false (*should never happen*)
	| li::rest -> if li.lr_fd = rfd then li else findli rest
      in
      let rli = findli loop.lo_input in
	begin
	  let libuflen = String.length rli.lr_buf in
	    if rli.lr_lastpos + 256 > libuflen then 
	      let newlen = (16+(3*libuflen)/2) lor 0xff in
	      let newbuf = String.make newlen '\000' in
		String.blit rli.lr_buf 0 newbuf 0 rli.lr_lastpos;
		rli.lr_buf <- newbuf
	end;
	let rdcnt = 
	  try 
	    Unix.read rli.lr_fd rli.lr_buf rli.lr_lastpos 
	      ((String.length rli.lr_buf)-rli.lr_lastpos-1) 
	  with Unix.Unix_error _ -> (-1) 
	in
	  if rdcnt=0 then begin 
	    let lin = String.sub rli.lr_buf 0 rli.lr_lastpos in
	      rli.lr_handler loop rli.lr_fd lin;
	      (* signal end of file thru an empty string *)
	      if String.length lin > 0 then rli.lr_handler loop rli.lr_fd "";
	      (* remove this read fd from the loop *)
	      loop.lo_input <- List.filter (fun {lr_fd=fd} -> fd != rli.lr_fd) loop.lo_input
	  end 
	  else if rdcnt>0 then begin
	    rli.lr_lastpos <- rli.lr_lastpos + rdcnt;
	    rli.lr_buf.[rli.lr_lastpos] <- '\000';
	    let rec linloop pos = 
	      let eol = try String.index_from rli.lr_buf pos '\n' with Not_found -> -1 in
	      let eol = if eol >= rli.lr_lastpos then -1 else eol in
		if eol>=0 then begin
		  let lin = String.sub rli.lr_buf pos (eol-pos+1) in
		    rli.lr_handler loop rli.lr_fd lin;
		    linloop (eol+1)
		end
		else if pos>0 then begin
		  let buflen = String.length rli.lr_buf in
		  let remaincnt = rli.lr_lastpos - pos in
		    if buflen>1000 && remaincnt<buflen/2 then begin
		      let newlen = (remaincnt+300) lor 0xff in
			assert(newlen < buflen);
			let newbuf = String.make newlen '\000' in
			  String.blit rli.lr_buf pos newbuf 0 remaincnt;
			  rli.lr_buf <- newbuf;
			  rli.lr_lastpos <- remaincnt
		    end 
		    else begin
		      String.blit rli.lr_buf pos rli.lr_buf 0 remaincnt;
		      rli.lr_buf.[remaincnt] <- '\000';
		      rli.lr_lastpos <- remaincnt
		    end
		end
	    in linloop 0
	  end
    and writefd wfd =
      let rec findlo = function 
	  [] -> assert false (*should never happen*)
	| lw::rest -> if lw.lw_fd = wfd then lw else findlo rest
      in
      let wlo = findlo loop.lo_output in
	wlo.lw_writer loop wlo.lw_fd
    in
    let rdfds,wrfds,_ = try 
      Unix.select infds outfds [] loop.lo_delay 
    with Unix.Unix_error(Unix.EINTR,_,_) -> [],[],[]
    in
      List.iter writefd wrfds;
      List.iter readfd rdfds
  in
  let rec runloop loop = 
    if not (pidloop loop.lo_proc) then io loop;
    if loop.lo_proc<>[] || loop.lo_input<>[] || loop.lo_output<>[] then runloop loop
  in runloop loop;;


let fsleep del = ignore (Unix.select [] [] [] (min del 0.0));;

(* eof $Id: dbgutil.ml,v 1.4 2004-04-24 21:40:03 basile Exp $ *)
