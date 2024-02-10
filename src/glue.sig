signature glue =
sig
  
  include Abbrev
  type mat = int Array2.array

  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : int * int -> IntInf.int -> IntInf.int -> thm
  val write_gluescripts : string -> int ->
    (int * int * int) -> (int * int * int) -> (int * int) -> unit

  (* potentially simpler problems *)
  val glue_pb_hole : int * int -> IntInf.int -> IntInf.int -> term
  val glue_hole : int * int -> IntInf.int -> IntInf.int -> thm

  (* export to external sat solvers *)
  val glue_hole_ext : int * int -> IntInf.int -> IntInf.int -> 
    ((int * int) * int) list list
  val write_dimacs : string -> ((int * int) * int) list list -> unit

end
