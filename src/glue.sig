signature glue =
sig
  
  include Abbrev
  type mat = int Array2.array
  val ramsey_clauses_mat : 
    int * int -> mat -> ((int * int) * int) list list

  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : int * int -> IntInf.int -> IntInf.int -> thm
  val write_gluescripts : string -> int ->
    (int * int * int) -> (int * int * int) -> (int * int) -> unit
  
  (* I/O for picosat *)
  val write_dimacs : string -> ((int * int) * int) list list -> unit
  val read_sol : string -> graph.coloring list
  val read_map : string -> (int, int * int) Redblackmap.dict

  (* benchmark *)
  val benchspec : 
    (unit, IntInf.int * IntInf.int, real * int) smlParallel.extspec
  val benchmark : string -> int -> IntInf.int list -> IntInf.int list -> unit
  
end
