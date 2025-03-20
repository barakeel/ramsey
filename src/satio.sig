signature satio =
sig
  
  include Abbrev

  val write_dimacs : string -> ((int * int) * int) list list -> unit
  val read_sol : string -> graph.coloring option
  val complete_graph : (int * int) -> graph.mat -> graph.mat option
  
end
