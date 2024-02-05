signature glue =
sig
  
  include Abbrev
  type mat = int Array2.array

  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : (int * int) -> IntInf.int -> IntInf.int -> thm
  val write_gluescripts : string -> int ->
    (int * int * int) -> (int * int * int) -> (int * int) -> unit

end
