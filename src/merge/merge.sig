signature merge =
sig
  
  include Abbrev
  type mat = graph.mat 
  
  val IMPOSSIBLE : int -> thm
  
end
