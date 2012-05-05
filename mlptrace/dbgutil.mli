(* file mlptrace/dbgutil.mli *)
(*** 
                                                                     
                           Objective Caml                           
                                                                    
      Basile Starynkevitch, projet Cristal, INRIA Rocquencourt      
                                                                    
  Copyright 2004 Institut National de Recherche en Informatique et  
  en Automatique.  All rights reserved.  This file is distributed   
  under the terms of the GNU Library General Public License, with   
  the special exception on linking described in file ../LICENSE.    
                                                                    
 ***)

val cvsid: string;;

module PtraceX86: sig 
  
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
end (*of Ptrace*) ;;

val get_symbol_table: string (*path of binary*) -> (string,Nativeint.t) Hashtbl.t * (Nativeint.t,string) Hashtbl.t;;

type 'a loop_t;;

(** split the words in a given string (from an optional position) - giving a string list *)
val split_words : ?pos: int -> string -> string list;;

(** create a loop *)
val make_loop : 'a -> 'a loop_t;;

(** get the pid waiting in the loop *)
val loop_pids : 'a loop_t -> int list;;

(** get the input fds in the loop *)
val loop_infds : 'a loop_t -> Unix.file_descr list;;

(** get the output fds in the loop *)
val loop_outfds : 'a loop_t -> Unix.file_descr list;;

(** get the wait delay *)
val loop_delay : 'a loop_t -> float;;

(** get the data *)
val loop_data : 'a loop_t -> 'a;;

(** add an input - the handler is called for every line *)
val loop_add_input : 'a loop_t -> Unix.file_descr 
  -> ('a loop_t -> Unix.file_descr ->  string -> unit)
  -> unit;;

(** remove an input (if it is there) *)
val loop_remove_input : 'a loop_t -> Unix.file_descr -> unit;;

(** add an output *)
val loop_add_output :  'a loop_t -> Unix.file_descr 
  -> ('a loop_t -> Unix.file_descr -> unit)
  -> unit;;

(** remove an output (if it is there) *)
val loop_remove_output : 'a loop_t -> Unix.file_descr -> unit;;


(** add a process *)
val loop_add_process : 'a loop_t -> int 
  -> ('a loop_t -> int * Unix.process_status -> unit)
  -> unit;;

(** remove a process *)
val loop_remove_process : 'a loop_t -> int -> unit;;

(** run the loop *)
val run_loop : 'a loop_t -> unit;;

val fsleep : float -> unit;;

(* eof $Id: dbgutil.mli,v 1.4 2004-04-24 21:40:08 basile Exp $ *)
