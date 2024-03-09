(* ===================================================================== *)
(* Merging lemmas to prove that degree 8 is impossible.                  *)
(* ===================================================================== *)

open HolKernel Abbrev boolLib Parse simpLib boolSimps BasicProvers
open aiLib kernel graph enum gen glue syntax sat
open ramseyDefTheory ramseyEnumTheory

val _ = new_theory "r45_degree8";

show_assums := true;
val R358 = DB.fetch "ramseyEnum" "R358";
val R4416 = DB.fetch "ramseyEnum" "R4416";
val R358p = prepare_rthm R358;
val g358l = filter is_gtm (hyp R358p);
val g358il = map_assoc (zip_mat o mat_of_gtm 8) g358l;
val R4416p = shift_rthm 8 (prepare_rthm R4416);
val g4416l = filter is_gtm (hyp R4416p);
val g4416il = map_assoc (zip_mat o mat_of_gtm_shifted 16) g4416l;
val C4524b_DEF = DB.fetch "ramseyDef" "C4524b_DEF";
val C4524r_DEF = DB.fetch "ramseyDef" "C4524r_DEF";
val C4524b_THM = (UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) C4524b_DEF;
val C4524r_THM = (UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) C4524r_DEF;
val IMP_FF = PROVE [] ``!x. (x ==> F) ==> F <=> x``;

fun IMPOSSIBLE_35 k g44il R44p g35i =
  let
    val elimthm = elim_exists k
    val (g35,m35i) = g35i
    val assume35 = ASSUME (mk_imp (g35,F))
    fun loop g44il thm = case g44il of [] => thm | (g44,m44i) :: m =>
      let
        val assume44 = DISCH g44 thm
        val thmname = "r45_" ^ infts m35i ^ "_" ^ infts m44i;
        val thyname = thmname;
        val thyfile = gluedir ^ "/" ^ thyname ^ "Theory";
        val _ = load thyfile;
        val gluethm3 = DB.fetch thyname thmname;
        val gluethm3' = PROVE_HYPL [C4524b_THM, C4524r_THM] gluethm3
        val gluethm = impossible_gluing k g35 g44 gluethm3'
        val conjthm = LIST_CONJ [assume35,assume44,gluethm]
        val newthm = Ho_Rewrite.PURE_ONCE_REWRITE_RULE [elimthm] conjthm
      in
        loop m newthm
      end
    val thm1 = loop g44il R44p
    val thm2 = PURE_ONCE_REWRITE_RULE [IMP_FF] (DISCH (mk_imp (g35,F)) thm1)
  in
    thm2
  end;

val gluedir = selfdir ^ "/work_glue358";
val lemmal =map (IMPOSSIBLE_35 8 g4416il R4416p) g358il)
val finalthm1 = PROVE_HYPL lemmal R358p
val finalthm2 = UNDISCH_ALL (BETA_RULE (DISCH_ALL finalthm1))
val lemma1 = ASSUME ``!(x:num) (y:num). E x y <=> E y x``; 
val lemma2 = GENL [``x:num``,``y:num``] (SPECL [``x + 8``,``y + 8``] lemma1);
val finalthm3 = PROVE_HYP lemma2 finalthm3;

val _ = save_thm ("r45_degree8", finalthm3);
val _ = export_theory ();


