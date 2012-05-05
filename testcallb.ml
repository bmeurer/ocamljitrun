(* file testcallb.ml *)
external test_cb : (int -> unit) -> int -> int -> unit = "test_callback";;
external test_msg : string -> int -> unit = "test_message";; 

let f i = test_msg "f in testcallb.ml" i
in test_cb f 1 3;;

test_msg "ended testcallb.ml" 0;;

(* eof $Id: testcallb.ml,v 1.4 2004-04-26 14:34:52 basile Exp $ *)
