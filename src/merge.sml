(* =========================================================================
   [C4524, C35k, C44(24-k)] |- F 
   ========================================================================= *)
 
structure merge :> merge =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph sat syntax

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

val L8_IMP_L24 = TAC_PROOF (([],``!x. x < 8 ==> x < 24``),
  SIMP_TAC arith_ss []);
    
val L16_IMP_ADD8_L24 = TAC_PROOF (([],``!y. y < 16 ==> y + 8 < 24``),
  SIMP_TAC arith_ss []);

val L8_DIFF_ADD8 = TAC_PROOF (([],``!x y. x < 8 ==> x <> y + 8``),
  SIMP_TAC arith_ss []);
  
val DIFF_IMP_DIFF_ADD8 = TAC_PROOF 
  (([], ``!ya yb. ya <> yb ==> ya + 8 <> yb + 8``),
  SIMP_TAC arith_ss []);

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
   Forward proof
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

(* -------------------------------------------------------------------------
   Adding assumptions about where the graphs are located.
   The 3,5 graph is on vertices less than 8.
   The 4,4 graph is on vertices greater or equal to 8.
   ------------------------------------------------------------------------- *)

(*
val C4524b_DEF = DB.fetch "ramseyDef" "C4524b_DEF";
val C4524r_DEF = DB.fetch "ramseyDef" "C4524r_DEF";
val C4524b_THM = (UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) C4524b_DEF;
val C4524r_THM = (UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL) C4524r_DEF;

fun get_clemma tm =
  let 
    val litl = fst (strip_imp tm) 
    val edgecl = map dest_lit litl 
    val nl = List.concat (map (fn ((a,b),_) => [a,b]) edgecl)
    val (il,b) = (mk_fast_set Int.compare nl, snd (hd edgecl) = 1)
    val cthm0 = if b then C4524b_THM else C4524r_THM
    val xl = map X il
  in
    DISCHL litl (UNDISCH_ALL (SPECL xl cthm0))
  end
*)

fun prove_shifting k gluethm3 = 
  let
    val xl = List.tabulate (k,X)
    val yl = List.tabulate (24-k,Y)
    val xyl = cartesian_product xl yl
    val yyl = all_pairs yl
    val intk = numSyntax.term_of_int k
    val gluethm4 = 
      INST (range (k,23,fn i => {redex = X i,residue = 
        numSyntax.mk_plus (Y (i-k), intk)})) gluethm3;
    val lemmal = map (fn x => UNDISCH (SPEC x L8_IMP_L24)) xl
    val gluethm5 = PROVE_HYPL lemmal gluethm4
    val lemmal = map (fn x => UNDISCH (SPEC x L16_IMP_ADD8_L24)) yl
    val gluethm6 = PROVE_HYPL lemmal gluethm5
    val lemmal = map (fn (a,b) => UNDISCH (SPECL [a,b] L8_DIFF_ADD8)) xyl;
    val gluethm7 = PROVE_HYPL lemmal gluethm6;
    val lemmal = map (fn (a,b) => UNDISCH (SPECL [a,b] DIFF_IMP_DIFF_ADD8)) yyl;
    val gluethm8 = PROVE_HYPL lemmal gluethm7
  in
    gluethm8
  end;

fun regroup_conjuncts k g35 g44 gluethm9 =
  let
    val conj35 = (fst o dest_imp o snd o strip_forall) g35
    val conj44 = (fst o dest_imp o snd o strip_forall) g44
    val xl = List.tabulate (k,X)
    val yl = List.tabulate (24-k,Y)
    val lemmal = CONJUNCTS (ASSUME conj35) @ CONJUNCTS (ASSUME conj44)
    val gluethm10 = PROVE_HYPL lemmal gluethm9;
    val _ = if length (hyp gluethm10) = 4 then () 
            else raise ERR "regroup_conjuncts" "1"
    val lemma = ASSUME (mk_conj (conj35,conj44));
    val lemmal = [CONJUNCT1 lemma, CONJUNCT2 lemma];
    val gluethm11 = PROVE_HYPL lemmal gluethm10;
    val _ = if length (hyp gluethm11) = 3 then () 
            else raise ERR "regroup_conjuncts" "2"
    fun test x = not (is_forall x) andalso not (is_cdeftm x)
    val gluethm12 = DISCHL (filter test (hyp gluethm11)) gluethm11
  in
    GENL (xl @ yl) gluethm12
  end;
  
fun impossible_gluing k g35 g44 gluethm3 =
  regroup_conjuncts k g35 g44 (prove_shifting k gluethm3)
  
end (* struct *)


