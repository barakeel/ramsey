(* =========================================================================
   Final step of the proof of R(4,5) = 25
   ========================================================================= *)

open HolKernel boolLib aiLib kernel gen sat syntax merge;
local open basicRamseyTheory r4524existTheory
  r45_degree8Theory r45_degree10Theory r45_degree12Theory
in end

(* ----------------------------------------------------------------------
   Impossibility of a vertex of degree 8,10 or 12. 
   Changing their shape to match hypothesis in ramsey_4_5_25_hyp.
   ---------------------------------------------------------------------- *)

val hypl = hyp ramsey_4_5_25_hyp
fun prec x = (fst o strip_imp o snd o strip_forall) x
val (hyp1,hyp2,hyp3,_) = quadruple_of_list hypl
val r45_degree8' = GEN E (DISCHL (prec hyp3) r45_degree8)
val r45_degree10' = GEN E (DISCHL (prec hyp1) r45_degree10)
val r45_degree12' = GEN E (DISCHL (prec hyp2) r45_degree12) 

(* ----------------------------------------------------------------------
   Remove hypothesis from ramsey_4_5_25_hyp to produce the final thm.
   ---------------------------------------------------------------------- *)

val r45_equals_25 = 
  PROVE_HYPL [r45_degree8',r45_degree10',r45_degree12',r4524exist]    
    ramsey_4_5_25_hyp

val _ = new_theory "r45_equals_25"
val _ = save_thm ("r45_equals_25", r45_equals_25)
val _ = export_theory ()
