signature satio =
sig
  
  include Abbrev

  val write_dimacs : string -> ((int * int) * int) list list -> unit
  val read_sol : string -> graph.coloring list

end
