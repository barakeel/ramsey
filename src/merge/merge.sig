signature merge =
sig
  
  include Abbrev
  type mat = graph.mat 
  

  (* serial version for k = 8 *)
  val IMPOSSIBLE : int -> thm
  val write_mergescript8 : unit -> unit
  
  (* parallel version *)  
  val IMPOSSIBLE_NTH_35 : int -> int -> thm
  val write_mergescripts : int -> unit
  
  val IMPOSSIBLE_REG_35 : int -> thm
  val write_regscript : int -> unit
  
end
