signature satio =
sig
  
  include Abbrev
 
  type edge = graph.edge
  type mat = graph.mat
  type coloring = graph.coloring

  (* problems *)
  val ramsey_clauses_fast : int * int -> mat -> coloring list
  exception ProofTimeout
  val complete_graph : real option -> (int * int) -> mat -> 
    (mat option * (real * int))
  val complete_graph_all : (int * int) -> mat -> coloring list 
  
  (* dimacs io *)
  val write_dimacs : string -> ((int * int) * int) list list -> unit
  val read_sol_cad : string -> coloring option
  val read_sol_bdd : string -> coloring list 
  val write_pdimacs : string -> (int * bool) list list -> unit
  val read_pdimacs : string -> (int * bool) list list
  
  (* initial split *)
  val mat_shift1 : mat -> mat
  val mat_vertex0 : int -> int -> mat
  val random_split : int * int * int * int -> mat
  
  (* cones *)
  val enum_mcone : mat -> coloring list
  val prove_cone : mat -> coloring -> (real * int)
  
  (* generalization *)  
  val count_graph : int * int -> mat -> int
  val count_gen : mat -> edge list -> int
  val prove_gen : real ->  mat -> int -> edge list -> (real * int) option
  val generalizable_edgel : mat -> mat -> edge list
  val loop_gen : mat -> edge list ->
    ((edge list * int) * (real * int)) * real ->
    ((edge list * int) * (real * int)) * real

  
  
end
