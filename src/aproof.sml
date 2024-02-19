(* =========================================================================
   [C4524, C358, C4416] |- F 
   ========================================================================= *)
   
load "kernel"; open aiLib kernel;
load "syntax"; open graph syntax;
load "sat"; open sat;
load "enumf/ramseyEnumTheory";
show_assums := true;

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

fun Y i = mk_var ("y" ^ its i, ``:num``)

fun rpt_fun_type_im n ty imty =
  if n <= 0 then imty else mk_type ("fun",[ty,rpt_fun_type_im (n-1) ty imty]);

fun pred_type n = rpt_fun_type_im n ``:num`` bool;

val x8 = List.tabulate (8,X);
val y16 = List.tabulate (16,Y);

val Eshift = ``\x y. (E (x+8) (y+8): bool)``;

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

fun shift_rthm rthm = 
  let
    val thm0 = INST [{redex = E, residue = Eshift}] rthm
    val gtml = filter is_gtm (hyp thm0)
    val conv1 = RENAME_VARS_CONV (map (fst o dest_var) y16)
    val conv2 = CONV_RULE (RATOR_CONV (RAND_CONV conv))
    fun f (gtm,thm) = (UNDISCH o conv2 o BETA_RULE o DISCH gtm) thm 
  in
    foldl f thm0 gtml
  end

(* -------------------------------------------------------------------------
   Propositional theorems and their mappings
   ------------------------------------------------------------------------- *)

(* getting the mapping for script files *)
val gluescriptl = filter (fn s => String.isSuffix "Script.sml" s) 
  (listDir (selfdir ^ "/glue8"));

fun get_gluemap gluescript =
  let
    val thyname = fst (split_string "Script" gluescript)
    val sl = readl (selfdir ^ "/glue8/" ^ gluescript);
    val sl1 = map (String.tokens (fn x => x = #"\"")) sl;
    val sl2 = filter (fn x => length x = 7) sl1;
    fun f x = 
      let 
        val g35 = stinf (List.nth (x,3))
        val g44 = stinf (List.nth (x,5))
        val thmname = List.nth (x,1)
      in
        ((g35,g44),(thyname,thmname))
      end
  in
    map f sl2
  end;

val glued = dnew (cpl_compare IntInf.compare IntInf.compare)
              (List.concat (map get_gluemap gluescriptl));

(* -------------------------------------------------------------------------
   Convert to first-order
   ------------------------------------------------------------------------- *)

fun to_first_order thm = 
  let
    fun get_atom x = if is_neg x then dest_neg x else x;
    val litl = mk_fast_set Term.compare 
      (List.concat (map (fst o strip_imp) (hyp thm)))
    val atoml = mk_fast_set Term.compare (map get_atom litl)
    fun sate_to_foe v = 
      let val (a,b,c) = (triple_of_list o String.tokens (fn x => x = #"_") 
        o fst o dest_var) v
      in
        hvarij (string_to_int b, string_to_int c)
      end
    fun f x = {redex = x, residue = sate_to_foe x}
    val sub = map f atoml
  in
    INST sub thm
  end;

(* -------------------------------------------------------------------------
   Adding assumptions about where the graphs are located.
   The 3,5 graph is on vertices less than 8.
   The 4,4 graph is on vertices greater or equal to 8.
   ------------------------------------------------------------------------- *)

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

fun create_gluethm (m35i,m44i) = 
  let
    val (thyname,thmname) = dfind (m35i,m44i) glued
    val _ = load ("glue8/" ^ thyname ^ "Theory")
    val gluethm1 = UNDISCH_SPLIT (DB.fetch thyname thmname)
    val lemmal = map (UNDISCH o snd o EQ_IMP_RULE o OR_IMP_CONV) (hyp gluethm1)
    val gluethm1' = PROVE_HYPL lemmal gluethm1
    val gluethm2 = to_first_order gluethm1'
    val lemmal = map get_clemma (hyp gluethm2)
    val gluethm3 = PROVE_HYPL lemmal gluethm2;
    val int8 = numSyntax.term_of_int 8;
    val gluethm4 = 
      INST (range (8,23,fn i => {redex = X i,residue = 
        numSyntax.mk_plus (Y (i-8), int8)})) gluethm3;
    val lemmal = map (fn x => UNDISCH (SPEC x L8_IMP_L24)) x8
    val gluethm5 = PROVE_HYPL lemmal gluethm4
    val lemmal = map (fn x => UNDISCH (SPEC x L16_IMP_ADD8_L24)) y16
    val gluethm6 = PROVE_HYPL lemmal gluethm5
    val lemmal = map (fn (a,b) => UNDISCH (SPECL [a,b] L8_DIFF_ADD8)) xyl;
    val gluethm7 = PROVE_HYPL lemmal gluethm6;
    val yyl = all_pairs y16;
    val lemmal = map (fn (a,b) => UNDISCH (SPECL [a,b] DIFF_IMP_DIFF_ADD8)) yyl;
    val gluethm8 = PROVE_HYPL lemmal gluethm7
  in
    gluethm8
  end



fun regroup_conjuncts conj35 conj44 gluethm9 =
  let
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
    GENL (x8 @ y16) gluethm12
  end;
  


(* -------------------------------------------------------------------------
   Preparing the two enumeration theorems and listing graphs
   ------------------------------------------------------------------------- *)

val R358 = DB.fetch "ramseyEnum" "R358";
val R4416 = DB.fetch "ramseyEnum" "R4416";

val R358p = prepare_rthm R358;
val g358l = filter is_gtm (hyp R358p);
val g358il = map_assoc (zip_mat o mat_of_gtm 8) g358l;

val R4416p = shift_rthm (prepare_rthm R4416);
val g4416l = filter is_gtm (hyp R4416p);
val g4416il = map_assoc (zip_mat o mat_of_gtm_shifted 16) g4416l;

val l = dict_sort (cpl_compare IntInf.compare IntInf.compare) 
  (cartesian_product (map snd g358il) (map snd g4416il));
if l = dkeys glued then () else raise ERR "" "";

(* -------------------------------------------------------------------------
   Proving that it is impossible to have a specific 3,5 graph
   by composing it with all possible 4,4 graphs
   ------------------------------------------------------------------------- *)

val IMP_FF = PROVE [] ``!x. (x ==> F) ==> F <=> x``;

fun IMPOSSIBLE_35 g35i =
  let
    val elimthm = elim_exists 8
    val (g35,m35i) = g35i
    val conj35 = (fst o dest_imp o snd o strip_forall) g35
    val assume35 = ASSUME (mk_imp (g35,F))
    fun loop g44il thm = case g44il of [] => thm | (g44,m44i) :: m =>
      let
        val conj44 = (fst o dest_imp o snd o strip_forall) g44
        val assume44 = DISCH g44 thm
        val gluethm = regroup_conjuncts conj35 conj44 
          (create_gluethm (m35i,m44i))
        val conjthm = LIST_CONJ [assume35,assume44,gluethm]
        val newthm = Ho_Rewrite.PURE_ONCE_REWRITE_RULE [elimthm] conjthm
      in
        loop m newthm
      end
    val thm1 = loop g4416il R4416p
    val thm2 = PURE_ONCE_REWRITE_RULE [IMP_FF] (DISCH (mk_imp (g35,F)) thm1)
  in
    thm2
  end;

(* -------------------------------------------------------------------------
   Final step
   ------------------------------------------------------------------------- *)

val finalthm = PROVE_HYPL (map IMPOSSIBLE_35 g358il) R358p;
val finalthm1 = UNDISCH_ALL (BETA_RULE (DISCH_ALL finalthm));

val lemma1 = ASSUME ``!(x:num) (y:num). E x y <=> E y x``; 
val lemma2 = GENL [``x:num``,``y:num``] (SPECL [``x + 8``,``y + 8``] lemma1);

val finalthm2 = PROVE_HYP lemma2 finalthm1;

(* -------------------------------------------------------------------------
   Theorem without the proof (requires C definitions)
   ------------------------------------------------------------------------- *)
(*
val finalthm2_alt = mk_thm 
   ([``!(x:num) (y:num). E x y <=> E y x``, 
     ``C358b E``, ``C358r E``, ``C4416b (\x y. E (x + 8) (y + 8))``,
     ``C4416r (\x y. E (x + 8) (y + 8))``, ``C4524b E``, ``C4524r E``]
    , F);
*)

(* -------------------------------------------------------------------------
   Check that the theorem created using mk_thm is equal to proper theorem
   ------------------------------------------------------------------------- *)

(*
term_eq (concl finalthm2) (concl finalthm2_alt);
list_compare Term.compare (hyp finalthm2,hyp finalthm2_alt);
*)



