signature satio =
sig
  
  include Abbrev

  val write_dimacs : string -> ((int * int) * int) list list -> unit
  
  val read_sol : string -> graph.coloring option
  val complete_graph : (int * int) -> graph.mat -> 
    (graph.mat option * (real * int))
   
  val write_pdimacs : string -> (int * bool) list list -> unit
  val read_pdimacs : string -> (int * bool) list list
  val all_cones54 : graph.mat -> (int * bool) list list
  
  val mat_shift1 : graph.mat -> graph.mat
  val mat_vertex0 : int -> int -> graph.mat
  val random_split : int * int * int * int -> graph.mat * graph.mat
  val prove_cone : 
    graph.mat * graph.mat -> (int * bool) list -> 
    graph.mat * (graph.mat option * (real * int))
    
  val count_graph : int * int -> graph.mat -> int
  val ramsey_clauses_fast : 
    int * int -> graph.mat -> ((int * int) * int) list list

  
end
