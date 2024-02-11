signature glue =
sig
  
  include Abbrev
  type mat = int Array2.array
  val ramsey_clauses_diagmat : int * int ->
    IntInf.int -> IntInf.int -> ((int * int) * int) list list
  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : int * int -> IntInf.int -> IntInf.int -> thm
  val write_gluescripts : string -> int ->
    (int * int * int) -> (int * int * int) -> (int * int) -> unit
  val write_dimacs : string -> ((int * int) * int) list list -> unit

end
