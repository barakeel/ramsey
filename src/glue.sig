signature glue =
sig
  
  include Abbrev
  type mat = graph.mat
  
  val ramsey_clauses_mat : 
    int * int -> mat -> ((int * int) * int) list list
  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : int * int -> IntInf.int -> IntInf.int -> thm
  val write_gluescripts : string -> int ->
    (int * int * int) -> (int * int * int) -> (int * int) -> unit
  
  (* benchmark *)
  val benchspec : (unit, IntInf.int * IntInf.int, real) smlParallel.extspec
  val benchmark : string -> int -> IntInf.int list -> IntInf.int list -> unit
  
end
