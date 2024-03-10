signature merge =
sig
  
  include Abbrev
  type mat = graph.mat 
  
  val IMPOSSIBLE_NTH_35 : int -> int -> thm
  val write_mergescripts : int -> unit
  val IMPOSSIBLE : int -> thm
  
end
