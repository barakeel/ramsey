(* =========================================================================
   Proves the existence of a graph satisfying r4524
   ========================================================================= *)

open HolKernel boolLib Parse simpLib boolSimps BasicProvers bossLib
open aiLib kernel syntax graph sat
local open ramseyDefTheory basicRamseyTheory in end

val ERR = mk_HOL_ERR "test";

val _ = new_theory "r4524exist" 

(* -------------------------------------------------------------------------
   Importing graph
   ------------------------------------------------------------------------- *)

fun read_mat () =
  let 
    val sl = readl (selfdir ^ "/r4524exist/r4524");
    fun f s = 
      map (fn x => if x = "F" then 2 else 1) (String.tokens Char.isSpace s);
    val ill = map f sl;
    val vv = Vector.fromList (map Vector.fromList ill);
    val m = mat_tabulate (Vector.length vv, (fn (i,j) => 
       if i = j then 0 else Vector.sub (Vector.sub (vv,i),j)));  
  in
    m
  end;

val m4524 = read_mat ();
val edgecl4524 = mat_to_edgecl m4524;

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

fun Eij (i,j) = list_mk_comb (E,[numSyntax.term_of_int i,numSyntax.term_of_int j]);
fun Eijc ((i,j),c) = 
  if c = 1 then (mk_conj (Eij (i,j), Eij (j,i)))
  else if c = 2 then (mk_conj (mk_neg (Eij (i,j)), mk_neg (Eij (j,i))))
  else raise ERR "Eijc" "";

val ivar = mk_var ("i",``:num``);
val jvar = mk_var ("j",``:num``);
fun ijtm (i,j) = 
  mk_conj (mk_eq (ivar, numSyntax.term_of_int i), 
           mk_eq (jvar, numSyntax.term_of_int j));
fun ijtm2 (i,j) = mk_disj (ijtm (i,j),ijtm (j,i));
fun ijctm ((i,j),c) = 
  if c = 1 then mk_conj (ijtm (i,j),ijtm (j,i))
  else if c = 2 then mk_neg (mk_conj (ijtm (i,j),ijtm (j,i)))
  else raise ERR "ijctm" "";


fun mk_domainl cliquen size =
  let
    val vl = List.tabulate (cliquen,X)
    fun f v = (v,numSyntax.mk_less (v,numSyntax.term_of_int size))
    val boundl = map f vl
    val pairvl = all_pairs vl
    val diffl = map (fn (a,b) => mk_neg (mk_eq (a,b))) pairvl
  in
    (boundl,diffl)
  end;

fun list_mk_forall_bound (boundl,tm) = case boundl of    
    [] => tm
  | (x,xbound) :: m => 
    mk_forall (x, mk_imp (xbound, list_mk_forall_bound (m,tm)))

fun nocliqueb size (cliquen,b) = 
  let
    val vl = List.tabulate (cliquen,X)
    val (boundl,diffl) = mk_domainl cliquen size
    val pairvl = all_pairs vl
    val litl = map (fn (a,b) => list_mk_comb (E,[a,b])) pairvl
    val litl' = map (fn x => if b then x else mk_neg x) litl
  in
    list_mk_forall_bound (boundl, list_mk_imp (diffl @ litl', F)) 
  end;
  
(* -------------------------------------------------------------------------
   Simple arithmetical theorems
   ------------------------------------------------------------------------- *)

val lesstml = List.tabulate (24,
  fn i => numSyntax.mk_less (numSyntax.term_of_int i, 
                              numSyntax.term_of_int 24));
val lessthml = map DECIDE lesstml; 
val difftml = cartesian_product (List.tabulate (24,I)) (List.tabulate (24,I)); 
val difftml2 = List.mapPartial (fn (a,b) => 
  if a = b then NONE
  else SOME (mk_neg (mk_eq (numSyntax.term_of_int a, numSyntax.term_of_int b)))) difftml; 
val diffthml = map DECIDE difftml2;

val interval = ``x < 24 <=> x < 6 \/ 
            (x >= 6 /\ x < 12) \/ 
            (x >= 12 /\ x < 18) \/
            (x >= 18 /\ x < 24)``;
val intervalthm = DECIDE interval;
val xvar = ``x:num``;
val xless6 = ``x < 6``;
val xdisj6 = list_mk_disj (List.tabulate (6, fn i => mk_eq (xvar, 
  numSyntax.term_of_int i)));
val disj6thm = DECIDE (mk_eq (xless6, xdisj6));
val xless12 = ``x >= 6 /\ x < 12``;
val xdisj12 = list_mk_disj (range (6, 11, fn i => mk_eq (xvar, 
  numSyntax.term_of_int i)));
val disj12thm = DECIDE (mk_eq (xless12, xdisj12));
val xless18 = ``x >= 12 /\ x < 18``;
val xdisj18 = list_mk_disj (range (12, 17, fn i => mk_eq (xvar, 
  numSyntax.term_of_int i)));
val disj18thm = DECIDE (mk_eq (xless18, xdisj18));
val xless24 = ``x >= 18 /\ x < 24``;
val xdisj24 = list_mk_disj (range (18, 23, fn i => mk_eq (xvar, 
  numSyntax.term_of_int i)));
val disj24thm = DECIDE (mk_eq (xless24, xdisj24));
val xlessfin = ``x < 24``;
val xdisjfin = list_mk_disj (List.tabulate (24, fn i => mk_eq (xvar, 
  numSyntax.term_of_int i)));
val disjthm = METIS_PROVE [intervalthm,disj6thm,disj12thm,disj18thm,disj24thm] (mk_forall (xvar, mk_eq (xlessfin, xdisjfin)));

val px = ``P (x:num) : bool``;
val P = mk_var ("P", ``:num -> bool``);
val disjP = list_mk_conj (List.tabulate (24, fn i => mk_comb (P,numSyntax.term_of_int i)));
val forallP = mk_forall (xvar, mk_imp (xdisjfin,px));

val disjforallthm = PROVE [] (mk_eq (disjP,forallP));

(* -------------------------------------------------------------------------
   Plan of the proof
   ------------------------------------------------------------------------- *)

val tm = ``(?(E: num -> num -> bool). P E) /\ (!(E: num -> num -> bool) . P E ==> Q E) ==> (?E. Q E)``;
val EXISTS_MP_THM = GENL (free_vars_lr tm)  (METIS_PROVE [] tm); 
    

(* -------------------------------------------------------------------------
   Proving the existence of the graph
   ------------------------------------------------------------------------- *)


val DISJ_SYM_INST = 
 GEN_ALL (SPECL [``x=(xi:num) /\ y=(yi:num)``,``y=(yi:num) /\ x=(xi:num)``] DISJ_SYM);

val OR_CONG_SIMPLE = PROVE []  
  ``!A C B D. (A = C) ==> (B = D) ==> ((A \/ B) <=> (C \/ D))``;

fun OR_CONG_RULE thm1 thm2 = 
  let 
    val (a,c) = dest_eq (concl thm1)
    val (b,d) = dest_eq (concl thm2)
    val thm3 = UNDISCH (UNDISCH (SPECL [a,c,b,d] OR_CONG_SIMPLE))
  in
    PROVE_HYPL [thm1,thm2] thm3
  end;
  
fun OR_CONG_LIST thml = case thml of 
    [] => raise ERR "OR_CONG_LIST" ""
  | [thm] => thm
  | thm :: m => OR_CONG_RULE thm (OR_CONG_LIST m);



fun create_exists () =
  let 
    val edgel = map fst (filter (fn x => snd x = 1) edgecl4524)
    val abstm = list_mk_abs ([ivar,jvar], list_mk_disj (map ijtm2 edgel))
    val ctm = list_mk_conj (map Eijc edgecl4524)
    val stm = ``!(x:num) (y:num). E x y <=> E y x``
    val cthm =
      let    
        val ctmsub = subst [{redex = E, residue = abstm}] ctm
        val cthm0 = REDEPTH_CONV BETA_CONV ctmsub
        val cthm1 = DECIDE ((rhs o concl) cthm0)
        val cthm2 = EQ_MP (SYM cthm0) cthm1
      in
        cthm2
      end
    val sthm =
      let 
        val stmsub = subst [{redex = E, residue = abstm}] stm
        val sthm0 = REDEPTH_CONV BETA_CONV stmsub
        val stmeq = (snd o strip_forall o rhs o concl) sthm0
        val (stm1,stm2) = dest_eq stmeq
        val stml1 = map list_mk_disj (mk_batch_full 2 (strip_disj stm1))
        val stml2 = map list_mk_disj (mk_batch_full 2 (strip_disj stm2))
        val seql = map mk_eq (combine (stml1,stml2))
        val seqthml = map (PROVE []) seql
        val sthm1 = GENL [``x:num``,``y:num``] (OR_CONG_LIST seqthml)
        val sthm2 = EQ_MP (SYM sthm0) sthm1
      in
        sthm2
      end 
   in
     EXISTS (mk_exists (E, mk_conj (stm,ctm)),abstm) (CONJ sthm cthm)
   end;


(* -------------------------------------------------------------------------
   Proving the forall part
   ------------------------------------------------------------------------- *)

fun test_diff vl = 
  not (null vl) andalso mem (hd vl) (tl vl)
 
fun test_red m vl = 
  if null vl orelse null (tl vl) then NONE else
  let val edgel = cartesian_product [hd vl] (tl vl) in
    List.find (fn (i,j) => mat_sub (m,i,j) = 2) edgel
  end

fun prove_mat_blue m vl depth tm =
  if test_diff vl
    then (TAC_PROOF (([],tm), SIMP_TAC bool_ss []))
  else case test_red m vl of
      SOME (i,j) => 
      let 
        val Eijl = map (mk_neg o Eij) [(i,j),(j,i)]      
        val imptm = list_mk_imp (Eijl,tm)
        (* val _ = print_endline (term_to_string imptm) *)
        val thm = TAC_PROOF (([],imptm), SIMP_TAC bool_ss [])
      in 
        UNDISCH (UNDISCH thm)
      end
    | NONE =>
    let
      val lambdatm =  mk_abs (X depth, (snd o dest_imp o snd o dest_forall) tm);
      val instthm = BETA_RULE 
        (INST [{redex = P, residue = lambdatm}] disjforallthm);
      val instthm' = (UNDISCH_SPLIT o fst o EQ_IMP_RULE) instthm;
      val tml = (strip_conj o lhs o concl) instthm
      fun f (x,vn) = prove_mat_blue m (vn :: vl) (depth + 1) x
      val lemmal = map f (number_snd 0 tml)
    in
      PROVE_HYPL lemmal instthm'
    end

fun test_blue m vl = 
  if null vl orelse null (tl vl) then NONE else
  let val edgel = cartesian_product [hd vl] (tl vl) in
    List.find (fn (i,j) => mat_sub (m,i,j) = 1) edgel
  end

fun prove_mat_red m vl depth tm =
  if test_diff vl
    then TAC_PROOF (([],tm), SIMP_TAC bool_ss [])
  else case test_blue m vl of
      SOME (i,j) => 
      let 
        val Eijl = map Eij [(i,j),(j,i)]      
        val imptm = list_mk_imp (Eijl,tm)
        val thm = TAC_PROOF (([],imptm), SIMP_TAC bool_ss [])
      in 
        UNDISCH (UNDISCH thm)
      end
    | NONE =>
    let
      val lambdatm =  mk_abs (X depth, (snd o dest_imp o snd o dest_forall) tm);
      val instthm = BETA_RULE 
        (INST [{redex = P, residue = lambdatm}] disjforallthm);
      val instthm' = (UNDISCH_SPLIT o fst o EQ_IMP_RULE) instthm;
      val tml = (strip_conj o lhs o concl) instthm
      fun f (x,vn) = prove_mat_red m (vn :: vl) (depth + 1) x
      val lemmal = map f (number_snd 0 tml)
    in
      PROVE_HYPL lemmal instthm'
    end
;

(* -------------------------------------------------------------------------
   Actual script
   ------------------------------------------------------------------------- *)

val _ = print_endline "blue cliques"
val blueclique = noclique 24 (4,true);
val bluecliqueb = nocliqueb 24 (4,true);
val bluecliqueeq = PURE_REWRITE_RULE [disjthm]
  (PROVE [] (mk_eq (blueclique,bluecliqueb)));
val bluetm = (rhs o concl) bluecliqueeq;
val thmblue1 = prove_mat_blue m4524 [] 0 bluetm;
val thmblue2 = EQ_MP (SYM bluecliqueeq) thmblue1;
val thmblue3 = PURE_REWRITE_RULE [GSYM disjthm] thmblue2;

val _ = print_endline "red cliques"
val redclique = noclique 24 (5,false);
val redcliqueb = nocliqueb 24 (5,false);
val redcliqueeq = PURE_REWRITE_RULE [disjthm]
  (PROVE [] (mk_eq (redclique,redcliqueb)));
val redtm = (rhs o concl) redcliqueeq;
val thmred1 = prove_mat_red m4524 [] 0 redtm;
val thmred2 = EQ_MP (SYM redcliqueeq) thmred1;
val thmred3 = PURE_REWRITE_RULE [GSYM disjthm] thmred2;

val _ = print_endline "exists thm"
val existsthm = create_exists (); 

val _ = print_endline "forall thm"
val lemmal = CONJUNCTS (ASSUME (snd (dest_exists (concl existsthm))));
val thm1 = PROVE_HYPL lemmal thmblue3;
val thm2 = PROVE_HYPL lemmal thmred3;
val thm3 = hd lemmal;
val thm4 = LIST_CONJ [thm3,thm1,thm2];
val thm5 = DISCH_ALL thm4;
val forallthm = GEN E thm5;

val _ = print_endline "combined"
val pabs = mk_abs (E, fst (dest_imp (concl thm5)));
val qabs = mk_abs (E, snd (dest_imp (concl thm5)));
val thm6 = BETA_RULE (SPECL [pabs,qabs] EXISTS_MP_THM);
val thm7 = MP thm6 (CONJ existsthm forallthm);
val C4524b_DEF = DB.fetch "ramseyDef" "C4524b_DEF";
val C4524r_DEF = DB.fetch "ramseyDef" "C4524r_DEF";
val SYM_DEF = DB.fetch "basicRamsey" "SYM_DEF";
val SYM_EQUIV = METIS_PROVE [] 
 ``(!(x:num) (y:num). E x y <=> E y x) = (!(x:num) (y:num). E x y ==> E y x)``;
val r4524exist = 
  save_thm ("r4524exist", PURE_REWRITE_RULE [SYM_EQUIV,GSYM SYM_DEF,GSYM C4524b_DEF, GSYM C4524r_DEF] thm7);

val _ = export_theory ();       
