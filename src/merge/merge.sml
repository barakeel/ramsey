(* =========================================================================
   [C4524, C35k, C44(24-k)] |- F 
   ========================================================================= *)
 
structure merge :> merge =
struct   

open HolKernel Abbrev boolLib bossLib ramseyDefTheory ramseyEnumTheory
open aiLib kernel graph sat syntax

val ERR = mk_HOL_ERR "merge"

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

fun Y i = mk_var ("y" ^ its i, ``:num``)

fun rpt_fun_type_im n ty imty =
  if n <= 0 then imty else mk_type ("fun",[ty,rpt_fun_type_im (n-1) ty imty]);

fun pred_type n = rpt_fun_type_im n ``:num`` bool;

fun lit_of_edgec ((i,j),c) = 
  if c = 1 then list_mk_comb (E,[X i,X j])
  else if c = 2 then mk_neg (list_mk_comb (E,[X i,X j]))
  else raise ERR "lit_of_edgec" ""
  
fun is_deftm s x = 
  is_comb x andalso 
  is_const (rator x) andalso 
  String.isPrefix s (fst (dest_const (rator x)))

fun is_gdeftm x = is_deftm "G" x;  
fun get_gdeftm thm = singleton_of_list (filter is_gdeftm (hyp thm))

fun is_cdeftm x = is_deftm "C" x;  

(* -------------------------------------------------------------------------
   Convert graph terms to matrices
   ------------------------------------------------------------------------- *)

fun is_gtm tm = is_forall tm andalso is_imp (snd (strip_forall tm))

fun litl_of_gtm gtm =
  let val tml = (strip_conj o fst o dest_imp o snd o strip_forall) gtm in
    filter is_lit tml
  end

fun get_ij atom = 
  let val (x1,x2) = pair_of_list (snd (strip_comb atom)) in
    (Xnum x1, Xnum x2)
  end;
 
fun dest_lit lit = 
  let 
    val b = is_neg lit 
    val atom = if b then dest_neg lit else lit
    val (i1,i2) = get_ij atom
  in
    ((i1,i2), if (not b) then 1 else 2)
  end

fun mat_of_gtm size gtm =
  edgecl_to_mat size (map dest_lit (litl_of_gtm gtm))

fun compare_lit (lit1,lit2) = 
  cpl_compare (cpl_compare Int.compare Int.compare) Int.compare
  (dest_lit lit1, dest_lit lit2)

(* -------------------------------------------------------------------------
   Convert shifted graph terms to matrices
   ------------------------------------------------------------------------- *)
 
fun get_ij_shifted atom = 
  let 
    val (t1,t2) = pair_of_list (snd (strip_comb atom)) 
    val f = Xnum o rand o rator
  in
    (f t1, f t2)
  end 
  
fun dest_lit_shifted lit =
  let 
    val b = is_neg lit 
    val atom = if b then dest_neg lit else lit
    val (i1,i2) = get_ij_shifted atom
  in
    ((i1,i2), if (not b) then 1 else 2)
  end
   
fun mat_of_gtm_shifted size gtm =
  edgecl_to_mat size (map dest_lit_shifted (litl_of_gtm gtm))

(* -------------------------------------------------------------------------
   Arithmetical theorems
   ------------------------------------------------------------------------- *)

local open numSyntax in

fun mk_Lk_IMP_L24 k = 
  let 
    val x = mk_var ("x",``:num``)
    val intk = term_of_int k
    val int24 = term_of_int 24;
    val tm = mk_forall (x, mk_imp (mk_less (x,intk),mk_less (x,int24)))
  in
    TAC_PROOF (([],tm), SIMP_TAC arith_ss [])
  end
    
fun mk_Lmk_IMP_ADDk_L24 k = 
  let 
    val y = mk_var ("y",``:num``)
    val intk = term_of_int k
    val intmk = term_of_int (24 - k)
    val int24 = term_of_int 24
    val atm = mk_plus (y,intk)
    val tm = mk_forall (y, mk_imp (mk_less (y,intmk), mk_less (atm,int24)))
  in
    TAC_PROOF (([],tm), SIMP_TAC arith_ss [])
  end

fun mk_Lk_DIFF_ADDk k = 
  let 
    val x = mk_var ("x",``:num``)
    val y = mk_var ("y",``:num``)
    val intk = term_of_int k
    val tm1 = mk_less (x,intk)
    val tm2 = mk_neg (mk_eq (x, mk_plus (y,intk)))
    val tm = list_mk_forall ([x,y], mk_imp (tm1,tm2))
  in
    TAC_PROOF (([],tm), SIMP_TAC arith_ss [])
  end
  
fun mk_DIFF_IMP_DIFF_ADDk k = 
  let 
    val intk = term_of_int k
    val ya = mk_var ("ya",``:num``)
    val yb = mk_var ("yb",``:num``)
    val tm1 = mk_neg (mk_eq (ya,yb))
    val tm2 = mk_neg (mk_eq (mk_plus (ya,intk), mk_plus (yb,intk)))
    val tm = list_mk_forall ([ya,yb], mk_imp (tm1,tm2))
  in
    TAC_PROOF (([],tm), SIMP_TAC arith_ss [])
  end

end (* local *)


(* -------------------------------------------------------------------------
   Convert !x. A => B => C to !x. A /\ B => C
   ------------------------------------------------------------------------- *)

fun IMP_AND_CONV tm = 
  let
    val vl = fst (strip_forall tm)
    val impl = (fst o strip_imp o snd o strip_forall) tm;
    val thm1 = (UNDISCH_ALL o SPEC_ALL o ASSUME) tm;
    val conj = list_mk_conj impl
    val lemmal = CONJUNCTS (ASSUME conj);
    val thm2 = PROVE_HYPL lemmal thm1;
    val thm3 = GENL vl (DISCH conj thm2);
    val thm4 = ASSUME (concl thm3)
    val thm5 = UNDISCH_SPLIT (SPEC_ALL thm4);
    val thm6 = GENL vl (DISCHL impl thm5)
  in
    IMP_ANTISYM_RULE (DISCH_ALL thm3) (DISCH_ALL thm6)
  end;

(* -------------------------------------------------------------------------
   Convert A \/ ~B \/ C to ~A => B => ~C => F
   ------------------------------------------------------------------------- *)

val NOT_NOT_THM = PROVE [] ``!x. ~(~x) <=> x``;
val OR_FALSE_THM = PROVE [] ``!x. x \/ F <=> x``;
fun OR_IMP_CONV tm = 
  let
    val alttm = list_mk_disj (strip_disj tm @ [F]) 
    val thm = PURE_REWRITE_CONV [DISJ_EQ_IMP] alttm
  in
    PURE_REWRITE_RULE [OR_FALSE_THM,NOT_NOT_THM] thm
  end

(* -------------------------------------------------------------------------
   ``((?x:num. R(x)) /\ (!x:num. R(x) ==> F)) ==> F``
   ------------------------------------------------------------------------- *)

fun elim_exists k =
  let 
    val P = mk_var ("P", rpt_fun_type_im k ``:num`` bool); 
    val Q = mk_var ("Q", rpt_fun_type_im (24 - k) ``:num`` bool); 
    val xl = List.tabulate (k,X);
    val yl = List.tabulate (24-k,Y);
    val Pa = list_mk_comb (P,xl);
    val Qa = list_mk_comb (Q,yl);
    val Pe = mk_imp (list_mk_forall (xl,mk_imp (Pa,F)), F);
    val Qe = mk_imp (list_mk_forall (yl,mk_imp (Qa,F)), F);
    val PQ = list_mk_forall (xl @ yl, mk_imp (mk_conj (Pa,Qa),F));
    val elim_exists_tm = mk_eq (list_mk_conj [Pe,Qe,PQ],F); 
  in
    PROVE [] elim_exists_tm
  end

(* -------------------------------------------------------------------------
   Making one gluing case correspond to the R35k and R44k theorems
   ------------------------------------------------------------------------- *)

fun prepare_rthm rthm =
  let 
    val gdeftm = get_gdeftm rthm
    val s = fst (dest_const (rator gdeftm))
    val thm0 = DISCH (get_gdeftm rthm) rthm
    val def = DB.fetch "ramseyDef" (s ^ "_DEF")
    val thm1 = PURE_ONCE_REWRITE_RULE [def] thm0
    val thm2 = UNDISCH_SPLIT thm1
    val gtml = filter is_gtm (hyp thm2)
    fun f (gtm,thm) = UNDISCH (PURE_REWRITE_RULE [IMP_AND_CONV gtm] 
      (DISCH gtm thm))
  in
    foldl f thm2 gtml
  end

fun shift_rthm k rthm = 
  let
    val intk = numSyntax.term_of_int k;
    val x = mk_var ("x",``:num``)
    val y = mk_var ("y",``:num``)
    val yl = List.tabulate (24-k,Y);
    val Eshift = list_mk_abs ([x,y],
      list_mk_comb (E, 
        [numSyntax.mk_plus (x,intk), numSyntax.mk_plus (y,intk)]))  
    val thm0 = INST [{redex = E, residue = Eshift}] rthm
    val gtml = filter is_gtm (hyp thm0)
    val conv1 = RENAME_VARS_CONV (map (fst o dest_var) yl)
    val conv2 = CONV_RULE (RATOR_CONV (RAND_CONV conv1))
    fun f (gtm,thm) = (UNDISCH o conv2 o BETA_RULE o DISCH gtm) thm 
  in
    foldl f thm0 gtml
  end

fun prove_shifting k arith gluethm3 = 
  let
    val xl = List.tabulate (k,X)
    val yl = List.tabulate (24-k,Y)
    val xyl = cartesian_product xl yl
    val yyl = all_pairs yl
    val intk = numSyntax.term_of_int k
    val (Lk_IMP_L24, Lmk_IMP_ADDk_L24, 
         Lk_DIFF_ADDk, DIFF_IMP_DIFF_ADDk) = arith
    val gluethm4 = 
      INST (range (k,23,fn i => {redex = X i,residue = 
        numSyntax.mk_plus (Y (i-k), intk)})) gluethm3;
    val lemmal = map (fn x => UNDISCH (SPEC x Lk_IMP_L24)) xl
    val gluethm5 = PROVE_HYPL lemmal gluethm4
    val lemmal = map (fn x => UNDISCH (SPEC x Lmk_IMP_ADDk_L24)) yl
    val gluethm6 = PROVE_HYPL lemmal gluethm5
    val lemmal = map (fn (a,b) => UNDISCH (SPECL [a,b] Lk_DIFF_ADDk)) xyl;
    val gluethm7 = PROVE_HYPL lemmal gluethm6;
    val lemmal = map (fn (a,b) => UNDISCH (SPECL [a,b] DIFF_IMP_DIFF_ADDk)) yyl;
    val gluethm8 = PROVE_HYPL lemmal gluethm7
  in
    gluethm8
  end;

fun regroup_conjuncts k g35 g44 gluethm9 =
  let
    val conj35 = (fst o dest_imp o snd o strip_forall) g35
    val conj44 = (fst o dest_imp o snd o strip_forall) g44
    val lemmal = CONJUNCTS (ASSUME conj35) @ CONJUNCTS (ASSUME conj44)
    val gluethm10 = PROVE_HYPL lemmal gluethm9;
    val _ = if length (hyp gluethm10) = 4 then () 
            else (show_assums := true;
                  raise ERR "regroup_conjuncts" 
                           ("1: " ^ (thm_to_string gluethm10)))
    val lemma = ASSUME (mk_conj (conj35,conj44));
    val lemmal = [CONJUNCT1 lemma, CONJUNCT2 lemma];
    val gluethm11 = PROVE_HYPL lemmal gluethm10;
    val _ = if length (hyp gluethm11) = 3 then () 
            else (show_assums := true; 
                  raise ERR "regroup_conjuncts" 
                           ("2: " ^ (thm_to_string gluethm11)))
    fun test x = not (is_forall x) andalso not (is_cdeftm x)
    val gluethm12 = DISCHL (filter test (hyp gluethm11)) gluethm11
  in
    GENL (List.tabulate (k,X) @ List.tabulate (24-k,Y)) gluethm12
  end;
  
fun impossible_gluing k arith g35 g44 gluethm3 =
  regroup_conjuncts k g35 g44 (prove_shifting k arith gluethm3)
  
(* -------------------------------------------------------------------------
   Differentiating between k=8,k=10 and k=12
   ------------------------------------------------------------------------- *)
 
val C4524b_THM = (UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) C4524b_DEF;
val C4524r_THM = (UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) C4524r_DEF;
  
fun mk_R35p k = 
  if k = 8 then prepare_rthm R358
  else if k = 10 then prepare_rthm R3510
  else if k = 12 then prepare_rthm R3512
  else raise ERR "mk_R35p" ("degree " ^ its k)
           
fun mk_R44p k =
  if k = 16 then shift_rthm k (prepare_rthm R4416) 
  else if k = 14 then shift_rthm k (prepare_rthm R4414)
  else if k = 12 then shift_rthm k (prepare_rthm R4412)
  else raise ERR "mk_R44p" ("degree " ^ its k)
  
fun mk_gluedir k = selfdir ^ "/work_glue35" ^ its k

val IMP_FF = PROVE [] ``!x. (x ==> F) ==> F <=> x``;

fun IMPOSSIBLE_35 k arith g44il elimthm R44p (g35,m35i) =
  let
    val gluedir = mk_gluedir k
    val assume35 = ASSUME (mk_imp (g35,F))
    fun loop g44il thm = case g44il of [] => thm | (g44,m44i) :: m =>
      let
        val assume44 = DISCH g44 thm
        val thmname = "r45_" ^ infts m35i ^ "_" ^ infts m44i;
        val thyname = thmname;
        val thyfile = gluedir ^ "/" ^ thyname ^ "Theory";
        val _ = load thyfile
        val gluethm3 = DB.fetch thyname thmname
        val gluethm3' = PROVE_HYPL [C4524b_THM, C4524r_THM] gluethm3
        val gluethm = impossible_gluing k arith g35 g44 gluethm3'
        val conjthm = LIST_CONJ [assume35,assume44,gluethm]
        val newthm = Ho_Rewrite.PURE_ONCE_REWRITE_RULE [elimthm] conjthm
      in
        loop m newthm
      end
    val thm1 = loop g44il R44p
    val thm2 = PURE_ONCE_REWRITE_RULE [IMP_FF] (DISCH (mk_imp (g35,F)) thm1)
  in
    thm2
  end

fun IMPOSSIBLE k =
  let
    val elimthm = elim_exists k
    val arith = (mk_Lk_IMP_L24 k, mk_Lmk_IMP_ADDk_L24 k, 
                 mk_Lk_DIFF_ADDk k, mk_DIFF_IMP_DIFF_ADDk k)
    val R35p = mk_R35p k
    val R44p = mk_R44p (24-k)
    val g35l = filter is_gtm (hyp R35p)
    val g35il = map_assoc (zip_mat o mat_of_gtm k) g35l
    val g44l = filter is_gtm (hyp R44p)
    val g44il = map_assoc (zip_mat o mat_of_gtm_shifted (24-k)) g44l
    val lemmal = map (IMPOSSIBLE_35 k arith g44il elimthm R44p) g35il
    val thm1 = PROVE_HYPL lemmal R35p
    val thm2 = UNDISCH_ALL (BETA_RULE (DISCH_ALL thm1))
    val lemma1 = ASSUME ``!(x:num) (y:num). E x y <=> E y x`` 
    val intk = numSyntax.term_of_int k
    val x = mk_var ("x",``:num``)
    val y = mk_var ("y",``:num``)
    val xpk = numSyntax.mk_plus (x,intk)
    val ypk = numSyntax.mk_plus (y,intk)
    val lemma2 = GENL [x,y] (SPECL [xpk,ypk] lemma1)
    val thm3 = PROVE_HYP lemma2 thm2
  in
    thm3
  end    

  
end (* struct *)


