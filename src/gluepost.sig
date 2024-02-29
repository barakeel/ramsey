signature gluepost =
sig
  
  include Abbrev
  type mat = graph.mat
  
  val post : thm -> thm
  
end
