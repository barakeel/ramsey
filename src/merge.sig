signature merge =
sig
  
  include Abbrev
  type mat = graph.mat 
    
  val prepare_rthm : thm -> thm
  val is_gtm : term -> bool
  val mat_of_gtm : int -> term -> mat
  val shift_rthm : int -> thm -> thm
  val mat_of_gtm_shifted : int -> term -> mat

  val elim_exists : int -> thm
  val impossible_gluing : int -> term -> term -> thm -> thm
  
end
