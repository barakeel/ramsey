signature satio =
sig
  
  include Abbrev
 
  type edge = graph.edge
  type mat = graph.mat
  type coloring = graph.coloring
  type clause = graph.coloring
  type gen = ((edge list * IntInf.int) * (real * int)) * IntInf.int
  
  (* problems *)
  val ramsey_clauses_fast : int * int -> mat -> coloring list
  exception ProofTimeout
  val complete_graph : bool -> real option -> clause list ->
    (int * int) -> mat -> (mat option * (real * int))
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
  val add_cone : mat -> coloring -> mat
  val enum_mcone : mat -> coloring list
  val select_cone : int * real -> clause list -> mat -> coloring list ->
     graph.coloring * gen
  

  
  (* generalization *)
  val score_gen : ('a * IntInf.int) * ('b * int) -> IntInf.int
  
  val prove_gen : real -> clause list -> mat -> int -> 
    edge list -> (real * int) option
  val generalizable_edgel : mat -> mat -> edge list
  val loop_gen : clause list -> mat -> edge list -> gen -> gen

  val generalize_string : string -> string
  val para_loop_gen : int -> mat -> edge list -> gen -> gen

  val subsumes : clause -> clause -> bool
  val mk_block : mat -> edge list -> gen -> clause
  val prove_conel : edge list -> mat -> clause list -> coloring list -> unit
  
  (* proving *)
  val prove_graph_string : string -> string
  val para_prove_cone : int -> graph.mat -> unit


  (* model counting  *)
  val mk_mcount_simple : mat -> edge list -> mat
  val write_count :  string -> clause list -> int * int -> mat -> unit
  val count_graph : clause list -> int * int -> mat -> IntInf.int
  val count_gen : clause list -> mat -> edge list -> IntInf.int
  val sample : mat -> ((int * int) * int) list -> mat * int
  val sample_string : string -> string
  val para_sample : int -> int -> mat -> edge list -> IntInf.int
  
end
