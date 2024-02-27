signature glue =
sig
  
  include Abbrev
  type mat = graph.mat
  
  val ramsey_clauses_mat : int * int -> mat -> ((int * int) * int) list list
  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : int * int -> IntInf.int -> IntInf.int -> thm

  (* benchmark *)
  val benchspec : (unit, IntInf.int * IntInf.int, real) smlParallel.extspec
  val benchmark : string -> int -> IntInf.int list -> IntInf.int list -> unit
  val benchmark_pbl : string -> (IntInf.int * IntInf.int) list -> unit
  val tune : string -> int * int * int * real * int * int -> unit
  
  (* creating theories *)
  val gluespec : (unit, IntInf.int * IntInf.int, real) smlParallel.extspec
  val order_pbl : IntInf.int list -> IntInf.int list -> 
    (IntInf.int * IntInf.int) list
  val glue_pbl : string -> (IntInf.int * IntInf.int) list -> unit
  
end
