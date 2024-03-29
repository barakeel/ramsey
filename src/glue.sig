signature glue =
sig
  
  include Abbrev
  type mat = graph.mat
  
  (* benchmark *)
  val benchspec : (unit, IntInf.int * IntInf.int, real) smlParallel.extspec
  val benchmark : string -> int -> IntInf.int list -> IntInf.int list -> unit
  val benchmark_pbl : string -> (IntInf.int * IntInf.int) list -> unit
  val tune : string -> int -> int * int * int * real -> unit
  val tune_3512 : string -> int -> int * int * real -> unit
  val tune_3510 : string -> int -> int * real -> unit
  val better_cover : string -> int * int * int * real -> unit
  
  (* calling sat solvers *)
  val ramsey_clauses_mat : int * int -> mat -> ((int * int) * int) list list
  val glue_pb : int * int -> IntInf.int -> IntInf.int -> term
  val glue : int * int -> IntInf.int -> IntInf.int -> thm
  val glue_pair : (IntInf.int * IntInf.int) -> thm (* does post-processing *)
  
  (* like Holmake but can limit the memory of each process *)
  val run_script_pbl : string -> (IntInf.int * IntInf.int) list -> unit
  
  (* I/O for problems *)
  val write_pbl : string -> (IntInf.int * IntInf.int) list-> unit
  val read_pbl : string -> (IntInf.int * IntInf.int) list

    
end
