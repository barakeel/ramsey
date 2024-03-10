signature merge =
sig
  
  include Abbrev
  type mat = graph.mat 
  

  (* serial version *)
  val IMPOSSIBLE : int -> thm

  (* parallel version *)  
  val IMPOSSIBLE_NTH_35 : int -> int -> thm
  val write_mergescripts : int -> unit
  val IMPOSSIBLE_REG_35 : int -> thm
  
  
end
