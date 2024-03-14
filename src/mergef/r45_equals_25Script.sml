(* =========================================================================
   Final step of the proof of R(4,5) = 25
   ========================================================================= *)

open HolKernel boolLib aiLib kernel gen sat syntax merge;
local open TheoryReaderDrop
  ramseyDefTheory basicRamseyTheory r45_degree8Theory r4524existTheory
in end;


(* ----------------------------------------------------------------------
   Work around to load theorems without growing the theory graph.
   ---------------------------------------------------------------------- *)

fun load_r45_degree10_theory n =   
  let 
    val thyname = "r45_degree10_" ^ its n
    val filedat = selfdir ^ "/merge3510/" ^ thyname ^ "Theory.dat"
  in
    TheoryReaderDrop.load_thydata_nolink thyname filedat;
    Theory.load_complete thyname
  end;

fun load_r45_degree12_theory n =   
  let 
    val thyname = "r45_degree12_" ^ its n
    val filedat = selfdir ^ "/merge3512/" ^ thyname ^ "Theory.dat"
  in
    TheoryReaderDrop.load_thydata_nolink thyname filedat;
    Theory.load_complete thyname
  end;

(* ----------------------------------------------------------------------
   Impossibility of a vertex of degree 8,10 or 12. 
   Changing their shape to match ramsey_4_5_25_hyp.
   Changing their shape to match hypothesis in ramsey_4_5_25_hyp.
   ---------------------------------------------------------------------- *)

val r45_degree8 = DB.fetch "r45_degree8" "r45_degree8";
val _ = ignore (List.tabulate (43,load_r45_degree10_theory));
val r45_degree10 = IMPOSSIBLE_REG_35 10;
val _ = ignore (List.tabulate (12,load_r45_degree12_theory));
val r45_degree12 = IMPOSSIBLE_REG_35 12;

val hypl = hyp basicRamseyTheory.ramsey_4_5_25_hyp;
fun prec x = (fst o strip_imp o snd o strip_forall) x;
val (hyp1,hyp2,hyp3,_) = quadruple_of_list hypl;

val r45_degree8' = GEN E (DISCHL (prec hyp3) r45_degree8);
val r45_degree10' = GEN E (DISCHL (prec hyp1) r45_degree10);
val r45_degree12' = GEN E (DISCHL (prec hyp2) r45_degree12);    

(* ----------------------------------------------------------------------
   Remove hypothesis from ramsey_4_5_25_hyp to produce the final thm.
   ---------------------------------------------------------------------- *)

val r45_equals_25 = 
  PROVE_HYPL [r45_degree8',r45_degree10',r45_degree12',r4524exist]    
    ramsey_4_5_25_hyp

val _ = new_theory "r45_equals_25"
val _ = save_thm ("r45_equals_25", r45_equals_25)
val _ = export_theory ()
