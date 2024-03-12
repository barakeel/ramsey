(* 
load "graph"; load "../def/ramseyDefTheory"; PolyML.print_depth 0;
*)

open aiLib kernel graph;
local open ramseyDefTheory in end 
open arithmeticTheory pred_setTheory;
open HolKernel boolLib Parse simpLib boolSimps BasicProvers proofManagerLib bossLib;
local open numTheory prim_recTheory SatisfySimps DefnBase in end;


chatting := false;

val _ = new_theory "basicRamsey";

val metis_ref = ref 0;
fun METIS_TAC thml goal = (incr metis_ref; 
                           metisTools.METIS_TAC thml goal)
  handle HOL_ERR e => 
    (print_endline (its (!metis_ref) ^ ": " ^ term_to_string (snd goal));
     raise HOL_ERR e)

(* -------------------------------------------------------------------------
   Definitions
   ------------------------------------------------------------------------- *)

val _ = print_endline "Definitions";

val sym = ``SYM (E:num -> num -> bool) = (!x:num. !y:num. E x y ==> E y x)``;
val sym_def = new_definition ("SYM_DEF",sym);

val hasclique = ``HASCLIQUE (r:num) (V:num -> bool) (E:num -> num -> bool) = (?U:num -> bool . (U SUBSET V /\ U HAS_SIZE r /\ (!x:num. !y:num . x IN U ==> y IN U ==> x <> y ==> E x y)))``;
val hasclique_def = new_definition ("HASCLIQUE_DEF",hasclique);

val hasanticlique = ``HASANTICLIQUE (r:num) (V:num -> bool) (E:num -> num -> bool) = HASCLIQUE r V (\x:num. \y:num. ~E x y)``;
val hasanticlique_def = new_definition ("HASANTICLIQUE_DEF",hasanticlique);

val ramseygraph = ``RAMSEYGRAPH (r:num) (s:num) (m:num) (V:num -> bool) (E:num -> num -> bool) = (V HAS_SIZE m /\ SYM E /\ ~HASCLIQUE r V E /\ ~HASANTICLIQUE s V E)``;
val ramseygraph_def = new_definition ("RAMSEYGRAPH_DEF",ramseygraph);

val ramseygraph_e1 = 
  METIS_PROVE [ramseygraph_def] ``RAMSEYGRAPH r s m V E ==> V HAS_SIZE m``;
val ramseygraph_e2 = 
  METIS_PROVE [ramseygraph_def] ``RAMSEYGRAPH r s m V E ==> SYM E``;
val ramseygraph_e3 = 
  METIS_PROVE [ramseygraph_def] ``RAMSEYGRAPH r s m V E ==> ~HASCLIQUE r V E``;
val ramseygraph_e4 = 
  METIS_PROVE [ramseygraph_def] 
    ``RAMSEYGRAPH r s m V E ==> ~HASANTICLIQUE s V E``;

val ramsey = ``RAMSEY (r:num) (s:num) (m:num) = (!V:num -> bool. !E:num -> num -> bool. !V:num->bool.!E:num->num->bool. ~RAMSEYGRAPH r s m V E)``;
val ramsey_def = new_definition ("RAMSEY_DEF",ramsey);

val rams = ``RAMS (r:num) (s:num) = (@m. RAMSEY r s m /\ (!n:num. n < m ==> ~RAMSEY r s n))``;
val rams_def = new_definition ("RAMS_DEF",rams);

val nbrs = ``NBRS (V:num -> bool) (E:num -> num -> bool) (x:num) (y:num) = (V y /\ y <> x /\ E x y)``;
val nbrs_def = new_definition ("NBRS_DEF",nbrs);

val antinbrs = ``ANTINBRS (V:num -> bool) (E:num -> num -> bool) (x:num) (y:num) = (V y /\ y <> x /\ ~E x y)``;
val antinbrs_def = new_definition ("ANTINBRS_DEF",antinbrs);

val hasdeg = ``HAS_DEG (V:num -> bool) (E:num -> num -> bool) (x:num) (n:num) = ((NBRS V E x) HAS_SIZE n)``;
val hasdeg_def = new_definition("HAS_DEG_DEF",hasdeg);

val hasantideg = ``HAS_ANTIDEG (V:num -> bool) (E:num -> num -> bool) (x:num) (n:num) = ((ANTINBRS V E x) HAS_SIZE n)``;
val hasantideg_def = new_definition("HAS_ANTIDEG_DEF",hasantideg);

val degr = ``DEGR (V:num -> bool) (E:num -> num -> bool) (x:num) = (CARD (NBRS V E x))``;
val degr_def = new_definition("DEGR_DEF",degr);

val antidegr = ``ANTIDEGR (V:num -> bool) (E:num -> num -> bool) (x:num) = (CARD (ANTINBRS V E x))``;
val antidegr_def = new_definition("ANTIDEGR_DEF",antidegr);

val c4524b_def = DB.fetch "ramseyDef" "C4524b_DEF";
val c4524r_def = DB.fetch "ramseyDef" "C4524r_DEF";

val c3510b_def = DB.fetch "ramseyDef" "C3510b_DEF";
val c3510r_def = DB.fetch "ramseyDef" "C3510r_DEF";
val c4414b_def = DB.fetch "ramseyDef" "C4414b_DEF";
val c4414r_def = DB.fetch "ramseyDef" "C4414r_DEF";

val c358b_def = DB.fetch "ramseyDef" "C358b_DEF";
val c358r_def = DB.fetch "ramseyDef" "C358r_DEF";
val c4416b_def = DB.fetch "ramseyDef" "C4416b_DEF";
val c4416r_def = DB.fetch "ramseyDef" "C4416r_DEF";

val c3512b_def = DB.fetch "ramseyDef" "C3512b_DEF";
val c3512r_def = DB.fetch "ramseyDef" "C3512r_DEF";
val c4412b_def = DB.fetch "ramseyDef" "C4412b_DEF";
val c4412r_def = DB.fetch "ramseyDef" "C4412r_DEF";

(* -------------------------------------------------------------------------
   R(2,m)
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(2,m)";

g `SYM E ==> y IN V ==> x IN NBRS V E y ==> y IN NBRS V E x`;
e (METIS_TAC [sym_def,nbrs_def,SPECIFICATION]);

val nbrs_swap = top_thm ();

g `x < n <=> x IN count n`;
e (simp []);
val in_count = top_thm ();

val sing_subset = METIS_PROVE [SUBSET_DEF,IN_SING] ``(x:num) IN V ==> {x} SUBSET V``;
val has_size_1 = METIS_PROVE [HAS_SIZE,SING,SING_IFF_CARD1] ``{(x:num)} HAS_SIZE 1``;

g `(U:num -> bool) HAS_SIZE n ==> ~(x IN U) ==> x INSERT U HAS_SIZE SUC n`;
e (rw [HAS_SIZE,CARD_DEF]);
val has_size_insert = top_thm ();

g `SUC 1 = 2`;
e decide_tac;
val suc_1_2 = top_thm ();

g `(x:num) <> y ==> ~(x IN {y})`;
e (simp []);
val not_in_sing = top_thm();

val has_size_2 = METIS_PROVE [not_in_sing,has_size_1,has_size_insert,suc_1_2] ``(x:num) <> y ==> {x; y} HAS_SIZE 2``;

val upair_subset = METIS_PROVE [SUBSET_DEF,UNION_SUBSET,INSERT_SING_UNION,sing_subset] ``(x:num) IN V ==> y IN V ==> {x;y} SUBSET V``;

val upair_e = METIS_PROVE [UNION_SUBSET,INSERT_SING_UNION,IN_SING,IN_UNION] ``(u:num) IN {x; y} ==> u = x \/ u = y``;

val has2clique_i_lem1 = METIS_PROVE [sym_def,upair_e] ``SYM E ==> E x y ==> x' IN {x; y} ==> y' IN {x; y} ==> x' <> y' ==> E x' y'``;

val has2clique_i_lem2 = METIS_PROVE [has_size_2,upair_subset,has2clique_i_lem1] ``SYM E ==> (x:num) IN V ==> y IN V ==> x <> y ==> E x y ==> ({x;y} SUBSET V /\ {x;y} HAS_SIZE 2 /\ (!x':num. !y':num . x' IN {x;y} ==> y' IN {x;y} ==> x' <> y' ==> E x' y'))``;

g `SYM E ==> (x:num) IN V ==> y IN V ==> x <> y ==> E x y ==> HASCLIQUE 2 V E`;
e (rw [hasclique_def]);
e (qexists_tac `{x; y}`);
e (METIS_TAC [has2clique_i_lem2]);
val has2clique_i = top_thm ();

val ramgraph2rmlem1 = METIS_PROVE [ramseygraph_def,has2clique_i] ``RAMSEYGRAPH 2 r m V E ==> (x:num) IN V ==> y IN V ==> x <> y ==> ~E x y``;

g `RAMSEYGRAPH 2 r m V E ==> HASANTICLIQUE m V E`;
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `V`);
e (simp [ramseygraph_def]);
e (METIS_TAC [ramseygraph_e1,ramgraph2rmlem1]);

val ramgraph2rmlem2 = top_thm ();

val ramsey_2_m_m = METIS_PROVE [ramsey_def,ramseygraph_e4,ramgraph2rmlem2] ``RAMSEY 2 m m``;

(* -------------------------------------------------------------------------
   Symmetry of the roles between cliques and anti-cliques
   ------------------------------------------------------------------------- *)

val _ = print_endline "Symmetry";

g `SYM E <=> SYM (\x y.~E x y)`;
e (rw [sym_def]);
e (METIS_TAC []);
val sym_compl = top_thm();

g `HASCLIQUE r V E <=> HASANTICLIQUE r V (\x y.~E x y)`;
e (rw [hasclique_def,hasanticlique_def]);
val hasclique_compl = top_thm();

g `HASANTICLIQUE r V E <=> HASCLIQUE r V (\x y.~E x y)`;
e (rw [hasclique_def,hasanticlique_def]);
val hasanticlique_compl = top_thm();

val ramseygraph_compl = METIS_PROVE [ramseygraph_def,sym_compl,hasclique_compl,hasanticlique_compl] ``RAMSEYGRAPH r s n V E <=> RAMSEYGRAPH s r n V (\x y.~E x y)``;

val ramsey_sym = METIS_PROVE [ramsey_def,ramseygraph_compl] ``RAMSEY r s n ==> RAMSEY s r n``;

val ramsey_m_2_m = METIS_PROVE [ramsey_2_m_m,ramsey_sym] ``RAMSEY m 2 m``;

(* -------------------------------------------------------------------------
   Theorem to connect HAS_SIZE n to BIJ f (count n)
   ------------------------------------------------------------------------- *)

val _ = print_endline "Bijections";

val bij_im_in = METIS_PROVE [in_count,BIJ_DEF,INJ_DEF] ``BIJ f (count n) (U:num -> bool) ==> x < n ==> f x IN U``;
val bij_im_inj = METIS_PROVE [in_count,BIJ_DEF,INJ_DEF] ``BIJ f (count n) (U:num -> bool) ==> x < n ==> y < n ==> f x = f y ==> x = y``;
val bij_im_surj = METIS_PROVE [in_count,BIJ_DEF,SURJ_DEF] ``BIJ f (count n) (U:num -> bool) ==> u IN U ==> ?x. x < n /\ f x = u``;

val has_size_bij = METIS_PROVE [FINITE_BIJ_COUNT,FINITE_BIJ_CARD,FINITE_COUNT,HAS_SIZE,CARD_COUNT] ``(U:num -> bool) HAS_SIZE n ==> ?f:num -> num. BIJ f (count n) U``;

g `BIJ f (count m) (U:num -> bool) ==> !n V. BIJ g (count n) (V:num -> bool) ==> U INTER V = EMPTY ==> ?h:num -> num. BIJ h (count (m + n)) (U ∪ V) /\ (!i. i < m ==> h i IN U) /\ (!j. m <= j ==> j < m + n ==> h j IN V)`;
e (rw [COUNT_SUC]);
e (qexists_tac `(\ i:num. if i < m then f i else g (i - m))`);
e BETA_TAC;
e CONJ_TAC;
e (rw [BIJ_DEF]);
e (rw [INJ_DEF]);
e IF_CASES_TAC;
e (METIS_TAC [bij_im_in,COUNT_applied,IN_APP]);
e (ASM_CASES_TAC ``i - m < n``);
e (METIS_TAC [bij_im_in,COUNT_applied,IN_APP]);
e decide_tac;
e (UNDISCH_TAC ``(if i < m then (f i:num) else g (i - m)) = (if i' < m then f i' else g (i' - m))``);
e IF_CASES_TAC;
e IF_CASES_TAC;
e (METIS_TAC [bij_im_inj]);
e (ASM_CASES_TAC ``i' - m < n``);
e DISCH_TAC;
e (ASM_CASES_TAC ``(f (i:num)):num IN U``);
e (ASM_CASES_TAC ``(g (i' - m)):num IN V``);
e (ASM_CASES_TAC ``(f (i:num)):num IN U INTER V``);
e (METIS_TAC [EMPTY_DEF,SPECIFICATION]);
e (UNDISCH_TAC ``~((f (i:num)):num IN U INTER V)``);
e (rw []);
e (METIS_TAC [bij_im_in]);
e (METIS_TAC [bij_im_in]);
e decide_tac;
e IF_CASES_TAC;
e DISCH_TAC;
e (ASM_CASES_TAC ``i - m < n``);
e (ASM_CASES_TAC ``(f (i':num)):num IN U``);
e (ASM_CASES_TAC ``(g (i - m)):num IN V``);
e (ASM_CASES_TAC ``(f (i':num)):num IN U INTER V``);
e (METIS_TAC [EMPTY_DEF,SPECIFICATION]);
e (UNDISCH_TAC ``~((f (i':num)):num IN U INTER V)``);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC [bij_im_in]);
e (METIS_TAC [bij_im_in]);
e decide_tac;
e (ASM_CASES_TAC ``i - m < n``);
e (ASM_CASES_TAC ``i' - m < n``);
e DISCH_TAC;
e (ASM_CASES_TAC ``i - m = i' - m``);
e decide_tac;
e (METIS_TAC [bij_im_inj]);
e decide_tac;
e decide_tac;
e (rw [SURJ_DEF]);
e IF_CASES_TAC;
e (METIS_TAC [bij_im_in]);
e (ASM_CASES_TAC ``i - m < n``);
e (METIS_TAC [bij_im_in]);
e decide_tac;
e (IMP_RES_TAC bij_im_surj);
e (qexists_tac `(x':num)`);
e (rw []);
e (IMP_RES_TAC bij_im_surj);
e (qexists_tac `x' + m`);
e (rw []);
e CONJ_TAC;
e (rw []);
e (METIS_TAC [bij_im_in]);
e (rw []);
e (ASM_CASES_TAC ``j - m < n``);
e (METIS_TAC [bij_im_in]);
e decide_tac;
val combine_count_bijs = top_thm ();

(* -------------------------------------------------------------------------
   Anti-neighbors
   ------------------------------------------------------------------------- *)

val _ = print_endline "Anti-neighbors";

g `0 < SUC n`;
e decide_tac;
val lt_0_S = top_thm ();

val inj_S_ne = METIS_PROVE [lt_0_S,in_count,INJ_DEF] ``INJ f (count (SUC s)) V ==> ?x:num.x IN V``;

val has_size_S_ne = METIS_PROVE [has_size_bij,BIJ_DEF,inj_S_ne] ``V HAS_SIZE SUC n ==> ?x:num.x IN V``;

g `HASCLIQUE r U E ==> U SUBSET V ==> HASCLIQUE r V E`;
e (rw [hasclique_def]);
e (METIS_TAC [SUBSET_TRANS]);
val hasclique_sub = top_thm ();

val hasanticlique_sub = METIS_PROVE [hasanticlique_def,hasclique_sub] ``HASANTICLIQUE s U E ==> U SUBSET V ==> HASANTICLIQUE s V E``;

val not_self_nbr = METIS_PROVE [nbrs_def,SPECIFICATION] ``~(v IN NBRS V E v)``;

val nbrs_sub = METIS_PROVE [nbrs_def,SPECIFICATION,SUBSET_DEF] ``NBRS V E v SUBSET V``;

val nbrs_finite = METIS_PROVE [nbrs_sub,INFINITE_SUBSET] ``FINITE V ==> FINITE (NBRS V E v)``;

g `SYM E ==> U SUBSET NBRS V E v ==> (!x:num. !y:num. x IN U ==> y IN U ==> x <> y ==> E x y) ==> (!x:num. !y:num. x IN v INSERT U ==> y IN v INSERT U ==> x <> y ==> E x y)`;
e (rw [sym_def,SUBSET_DEF,SPECIFICATION,nbrs_def]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val sub_nbrs_cliq = top_thm();

val insert_subset_1 = METIS_PROVE [INSERT_SUBSET] ``(v:num) IN V ==> U SUBSET V ==> v INSERT U SUBSET V``;
val insert_subset_2 = METIS_PROVE [insert_subset_1,nbrs_sub,SUBSET_TRANS] ``(v:num) IN V ==> U SUBSET NBRS V E v ==> v INSERT U SUBSET V``;

g `SYM E ==> v IN V ==> HASCLIQUE r (NBRS V E v) E ==> HASCLIQUE (SUC r) V E`;
e (rw [hasclique_def]);
e (qexists_tac `v INSERT U`);
e CONJ_TAC;
e (METIS_TAC [insert_subset_2]);
e CONJ_TAC;
e (METIS_TAC [has_size_insert,not_self_nbr,nbrs_sub,SUBSET_DEF]);
e (METIS_TAC [sub_nbrs_cliq]);
val sub_nbrs_hasclique = top_thm();

val ramseygraph_nbrs = METIS_PROVE [hasanticlique_sub,nbrs_sub,sub_nbrs_hasclique,ramseygraph_def,hasdeg_def] ``RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> HAS_DEG V E x d ==> RAMSEYGRAPH r s d (NBRS V E x) E``;

val not_self_antinbr = METIS_PROVE [antinbrs_def,SPECIFICATION] ``~(v IN ANTINBRS V E v)``;

val antinbrs_sub = METIS_PROVE [antinbrs_def,SPECIFICATION,SUBSET_DEF] ``ANTINBRS V E v SUBSET V``;

g `SYM E ==> U SUBSET ANTINBRS V E v ==> (!x:num. !y:num. x IN U ==> y IN U ==> x <> y ==> ~E x y) ==> (!x:num. !y:num. x IN v INSERT U ==> y IN v INSERT U ==> x <> y ==> ~E x y)`;
e (rw [sym_def,SUBSET_DEF,SPECIFICATION,antinbrs_def]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val sub_antinbrs_anticliq = top_thm();

val insert_subset_3 = METIS_PROVE [insert_subset_1,antinbrs_sub,SUBSET_TRANS] ``(v:num) IN V ==> U SUBSET ANTINBRS V E v ==> v INSERT U SUBSET V``;

g `SYM E ==> v IN V ==> HASANTICLIQUE r (ANTINBRS V E v) E ==> HASANTICLIQUE (SUC r) V E`;
e (rw [hasclique_def,hasanticlique_def]);
e (qexists_tac `v INSERT U`);
e CONJ_TAC;
e (METIS_TAC [insert_subset_3]);
e CONJ_TAC;
e (METIS_TAC [has_size_insert,not_self_antinbr,antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC [sub_antinbrs_anticliq]);
val sub_antinbrs_hasanticlique = top_thm();

val ramseygraph_antinbrs = METIS_PROVE [hasclique_sub,antinbrs_sub,sub_antinbrs_hasanticlique,ramseygraph_def,hasantideg_def] ``RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> RAMSEYGRAPH r s d (ANTINBRS V E x) E``;

g `NBRS V E v UNION ANTINBRS V E v = V DELETE v`;
e (rw [EXTENSION,DELETE_DEF,DIFF_DEF,nbrs_def,antinbrs_def,UNION_DEF,SPECIFICATION]);
e (METIS_TAC []);
val nbrs_antinbrs_union = top_thm ();

g `NBRS V E v INTER ANTINBRS V E v = EMPTY`;
e (rw [EXTENSION,EMPTY_DEF,nbrs_def,antinbrs_def,INTER_DEF,SPECIFICATION]);
e (METIS_TAC []);
val nbrs_antinbrs_inter = top_thm ();

g `V HAS_SIZE SUC n ==> x IN V ==> HAS_DEG V E x d ==> HAS_ANTIDEG V E x d' ==> CARD (NBRS V E x UNION ANTINBRS V E x) + CARD (NBRS V E x INTER ANTINBRS V E x) = n ==> d + d' = n`;
e (rw [HAS_SIZE,hasdeg_def,hasantideg_def,CARD_UNION]);
val deg_antideg_sum_lem1 = top_thm ();

g `V HAS_SIZE SUC n ==> x IN V ==> HAS_DEG V E x d ==> HAS_ANTIDEG V E x d' ==> CARD (NBRS V E x UNION ANTINBRS V E x) + CARD (NBRS V E x INTER ANTINBRS V E x) = n`;
e (rw [HAS_SIZE,nbrs_antinbrs_union,nbrs_antinbrs_inter]);
val deg_antideg_sum_lem2 = top_thm ();

val deg_antideg_sum = METIS_PROVE [deg_antideg_sum_lem1,deg_antideg_sum_lem2] ``V HAS_SIZE SUC n ==> x IN V ==> HAS_DEG V E x d ==> HAS_ANTIDEG V E x d' ==> d + d' = n``;

val ramseygraph_nbrs_finite = METIS_PROVE [SUBSET_FINITE,nbrs_sub,ramseygraph_e1,HAS_SIZE] ``RAMSEYGRAPH r s n V E ==> FINITE (NBRS V E x)``;

val nbrs_card_deg = METIS_PROVE [ramseygraph_nbrs_finite,hasdeg_def,FINITE_HAS_SIZE] ``RAMSEYGRAPH r s n V E ==> HAS_DEG V E x (CARD (NBRS V E x))``;

val ramseygraph_antinbrs_finite = METIS_PROVE [SUBSET_FINITE,antinbrs_sub,ramseygraph_e1,HAS_SIZE] ``RAMSEYGRAPH r s n V E ==> FINITE (ANTINBRS V E x)``;

val antinbrs_card_deg = METIS_PROVE [ramseygraph_antinbrs_finite,hasantideg_def,FINITE_HAS_SIZE] ``RAMSEYGRAPH r s n V E ==> HAS_ANTIDEG V E x (CARD (ANTINBRS V E x))``;

val deg_antideg_sum_card = METIS_PROVE [deg_antideg_sum,nbrs_card_deg,antinbrs_card_deg,ramseygraph_e1] ``RAMSEYGRAPH r s (SUC n) V E ==> x IN V ==> CARD (NBRS V E x) + CARD (ANTINBRS V E x) = n``;

val ramseygraph_sub = METIS_PROVE [ramseygraph_def,hasclique_sub,hasanticlique_sub] ``RAMSEYGRAPH r s n V E ==> U SUBSET V ==> U HAS_SIZE m ==> RAMSEYGRAPH r s m U E``;

val inj_count_leq = METIS_PROVE [COUNT_MONO,INJ_SUBSET,SUBSET_REFL] ``INJ f (count n) V ==> m <= n ==> INJ f (count m) V``;

val inj_image_count_sub = METIS_PROVE [INJ_IMAGE_SUBSET] ``INJ f (count m) V ==> IMAGE f (count m) SUBSET V``;

val inj_image_count_has_size = METIS_PROVE [FINITE_COUNT,CARD_COUNT,INJ_CARD_IMAGE_EQ,IMAGE_FINITE,HAS_SIZE] ``INJ f (count m) V ==> IMAGE f (count m) HAS_SIZE m``;

g `INJ f (U:num -> bool) (V:num -> bool) ==> U' SUBSET U ==> U' HAS_SIZE m ==> IMAGE f U' HAS_SIZE m`;
e (rw [HAS_SIZE]);
e (ASM_CASES_TAC ``INJ f (U':num -> bool) (V:num -> bool)``);
e (METIS_TAC [INJ_CARD_IMAGE]);
e (METIS_TAC [INJ_SUBSET,SUBSET_REFL]);
val inj_image_sub_has_size = top_thm ();

(* -------------------------------------------------------------------------
   R(a,b) <= R(a-1,b) + R(a,b-1)
   ------------------------------------------------------------------------- *)

val _ = print_endline "Upper bound";

val ramseygraph_mon_lem1 = METIS_PROVE [inj_image_count_sub,inj_image_count_has_size,inj_count_leq,ramseygraph_sub] ``RAMSEYGRAPH r s n V E ==> INJ f (count n) V ==> m <= n ==> RAMSEYGRAPH r s m (IMAGE f (count m)) E``;
val ramseygraph_mon_lem2 = METIS_PROVE [ramseygraph_mon_lem1] ``RAMSEYGRAPH r s n V E ==> INJ f (count n) V ==> m <= n ==> ?U.RAMSEYGRAPH r s m U E``;

val ramseygraph_mon = METIS_PROVE [ramseygraph_mon_lem2,has_size_bij,ramseygraph_e1,BIJ_DEF] ``RAMSEYGRAPH r s n V E ==> m <= n ==> ?U.RAMSEYGRAPH r s m U E``;

val ramsey_mon = METIS_PROVE [ramsey_def,ramseygraph_mon] ``RAMSEY r s m ==> m <= n ==> RAMSEY r s n``;

val ramseygraph_deg_bd_lem1 = METIS_PROVE [ramseygraph_nbrs,ramsey_def] ``RAMSEY r s d ==> RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> HAS_DEG V E x d ==> F``;

val ramseygraph_deg_bd_lem2 = METIS_PROVE [ramseygraph_deg_bd_lem1,ramsey_mon] ``RAMSEY r s m ==> RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> HAS_DEG V E x d ==> ~(m <= d)``;

g `~(m <= n) ==> n < m`;
e decide_tac;
val not_leq_less = top_thm ();

val ramseygraph_deg_bd = METIS_PROVE [ramseygraph_deg_bd_lem2,not_leq_less] ``RAMSEY r s m ==> RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> HAS_DEG V E x d ==> d < m``;

val ramseygraph_deg_card_bd = METIS_PROVE [ramseygraph_deg_bd,nbrs_card_deg] ``RAMSEY r s m ==> RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> CARD (NBRS V E x) < m``;

val ramseygraph_antideg_bd_lem1 = METIS_PROVE [ramseygraph_antinbrs,ramsey_def] ``RAMSEY r s d ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> F``;

val ramseygraph_antideg_bd_lem2 = METIS_PROVE [ramseygraph_antideg_bd_lem1,ramsey_mon] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> ~(m <= d)``;

val ramseygraph_antideg_bd = METIS_PROVE [ramseygraph_antideg_bd_lem2,not_leq_less] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> d < m``;

val ramseygraph_antideg_card_bd = METIS_PROVE [ramseygraph_antideg_bd,antinbrs_card_deg] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> CARD (ANTINBRS V E x) < m``;

g `k < l ==> m + k < m + l`;
e decide_tac;
val add_lt_l = top_thm ();

val ramseygraph_deg_card_lower_bd = METIS_PROVE [ramseygraph_antideg_card_bd,deg_antideg_sum_card,add_lt_l] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) (SUC n) V E ==> x IN V ==> n < CARD (NBRS V E x) + m``;

g `SUC (m + n) < d + SUC m ==> d < SUC n ==> F`;
e decide_tac;
val ramsey_sum_lem1 = top_thm ();

val ramsey_sum_lem2 = METIS_PROVE [ramseygraph_deg_card_lower_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> x IN V ==> SUC (m + n) < CARD (NBRS V E x) + (SUC m)``;

val ramsey_sum_lem3 = METIS_PROVE [ramseygraph_deg_card_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> x IN V ==> CARD (NBRS V E x) < SUC n``;

val ramsey_sum_lem4 = METIS_PROVE [ramsey_sum_lem1,ramsey_sum_lem2,ramsey_sum_lem3] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> x IN V ==> F``;

val ramsey_sum_lem5 = METIS_PROVE [ramsey_sum_lem4,has_size_S_ne,ramseygraph_e1] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> F``;

val ramsey_sum = METIS_PROVE [ramsey_sum_lem5,ramsey_def] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEY (SUC r) (SUC s) (SUC (SUC (m + n)))``;

(* -------------------------------------------------------------------------
   R(3,3) <= 6
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,3) <= 6";

g `RAMSEY 0 s 0`;
e (rw [ramsey_def,ramseygraph_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``HASCLIQUE 0 V E``);
e (METIS_TAC []);
e (UNDISCH_TAC ``~HASCLIQUE 0 V E``);
e (rw [hasclique_def]);
e (qexists_tac `(EMPTY:num -> bool)`);
e (rw []);
e (METIS_TAC [HAS_SIZE_0]);
val ramsey_0_s_0 = top_thm ();

g `BIJ f (count m) (U:num -> bool) ==> i < m ==> f i IN U`;
e (rw [BIJ_DEF,INJ_DEF]);
val bij_count_in = top_thm ();

g `BIJ f (count m) (U:num -> bool) ==> i < m ==> j < m ==> i <> j ==> f i <> f j`;
e (rw [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
val bij_count_neq = top_thm ();

g `RAMSEY 1 s 1`;
e (rw [ramsey_def,ramseygraph_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``HASCLIQUE 1 V E``);
e (METIS_TAC []);
e (UNDISCH_TAC ``~HASCLIQUE 1 V E``);
e (rw [hasclique_def]);
e (ASM_CASES_TAC ``(V:num -> bool) HAS_SIZE 1``);
e (IMP_RES_TAC has_size_bij);
e (qexists_tac `{f 0}`);
e (rw []);
e (ASM_CASES_TAC ``0 < 1``);
e (METIS_TAC [bij_count_in]);
e decide_tac;
e (rw [HAS_SIZE]);
e (METIS_TAC []);
val ramsey_1_s_1 = top_thm ();

g `!r s. ?m. RAMSEY r s (SUC m)`;
e Induct;
e GEN_TAC;
e (qexists_tac `0`);
e (ASM_CASES_TAC ``SUC 0 = 1``);
e (ASM_CASES_TAC ``RAMSEY 0 s 1``);
e (METIS_TAC []);
e (ASM_CASES_TAC ``0 <= 1``);
e (METIS_TAC [ramsey_0_s_0,ramsey_mon]);
e decide_tac;
e decide_tac;
e Induct;
e (qexists_tac `0`);
e (ASM_CASES_TAC ``SUC 0 = 1``);
e (ASM_CASES_TAC ``RAMSEY (SUC r) 0 1``);
e (METIS_TAC []);
e (ASM_CASES_TAC ``0 <= 1``);
e (METIS_TAC [ramsey_0_s_0,ramsey_mon,ramsey_sym]);
e decide_tac;
e decide_tac;
e (ASM_CASES_TAC ``?n. RAMSEY r (SUC s) (SUC n)``);
e (UNDISCH_TAC ``?n. RAMSEY r (SUC s) (SUC n)``);
e (UNDISCH_TAC ``?m. RAMSEY (SUC r) s (SUC m)``);
e (METIS_TAC [ramsey_sum]);
e (METIS_TAC []);
val ramsey_ex = top_thm ();

g `!n:num. (?i:num. i < n /\ p i) ==> ?m:num. p m /\ !k:num. k < m ==> ~p k`;
e Induct;
e (rw []);
e (rw []);
e (ASM_CASES_TAC ``?i. i < n /\ p i``);
e (METIS_TAC []);
e (qexists_tac `(i:num)`);
e (rw []);
e DISCH_TAC;
e (UNDISCH_TAC ``~?i. i < n /\ p i``);
e (simp []);
e (qexists_tac `(k:num)`);
e (rw []);
val least_num_thm = top_thm ();

g `!r s. ?m. RAMSEY r s m /\ !n. n < m ==> ~RAMSEY r s n`;
e (METIS_TAC [least_num_thm,ramsey_ex]);
val ramsey_ex_least = top_thm ();

g `RAMSEY r s (RAMS r s) /\ !n:num. n < RAMS r s ==> ~RAMSEY r s n`;
e (simp [rams_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``?p:num -> bool . ~p (@ m. p m) /\ (?m. p m)``);
e (METIS_TAC [SELECT_AX]);
e (UNDISCH_TAC ``~?p:num -> bool . ~p (@ m. p m) /\ (?m. p m)``);
e (simp []);
e (qexists_tac `\m:num. RAMSEY r s m /\ !n. n < m ==> ~RAMSEY r s n`);
e BETA_TAC;
e CONJ_TAC;
e (METIS_TAC []);
e (METIS_TAC [ramsey_ex_least]);
val rams_prop = top_thm ();

g `~RAMSEY r s n ==> RAMSEY r s (SUC n) ==> RAMS r s = SUC n`;
e (rw []);
e CCONTR_TAC;
e (ASM_CASES_TAC ``SUC n < RAMS r s``);
e (METIS_TAC [rams_prop]);
e (ASM_CASES_TAC ``RAMS r s <= n``);
e (METIS_TAC [ramsey_mon,rams_prop]);
e decide_tac;
val rams_eq_S = top_thm ();

g `SUC 2 = 3`;
e decide_tac;
val suc_2_3 = top_thm ();

g `SUC (SUC (2 + 2)) = 6`;
e decide_tac;
val suc_suc_2_2_6 = top_thm ();

val ramsey_S2_S2_SS22 = METIS_PROVE [ramsey_sum,ramsey_2_m_m,ramsey_m_2_m] ``RAMSEY (SUC 2) (SUC 2) (SUC (SUC (2 + 2)))``;

val ramsey_3_3_6 = METIS_PROVE [ramsey_S2_S2_SS22,suc_2_3,suc_suc_2_2_6] ``RAMSEY 3 3 6``;

(* -------------------------------------------------------------------------
   R(3,4,9) implies all vertices have degree 3
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,4,9) implies all vertices have degree 3";

g `m + n < d + SUC m ==> d < SUC n ==> d = n`;
e decide_tac;
val ramsey_sum_regular_lem1 = top_thm ();

val ramsey_sum_regular_lem2 = METIS_PROVE [ramseygraph_deg_card_lower_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (m + n)) V E ==> x IN V ==> m + n < CARD (NBRS V E x) + (SUC m)``;

val ramsey_sum_regular_lem3 = METIS_PROVE [ramseygraph_deg_card_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (m + n)) V E ==> x IN V ==> CARD (NBRS V E x) < SUC n``;

val ramsey_sum_regular = METIS_PROVE [ramsey_sum_regular_lem1,ramsey_sum_regular_lem2,ramsey_sum_regular_lem3] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (m + n)) V E ==> x IN V ==> CARD (NBRS V E x) = n``;

val ramseygraph_3_4_9_3regular_lem1 = METIS_PROVE [ramsey_sum_regular] ``RAMSEY (SUC 2) 3 (SUC 5) ==> RAMSEY 2 (SUC 3) (SUC 3) ==> RAMSEYGRAPH (SUC 2) (SUC 3) (SUC (5 + 3)) V E ==> x IN V ==> CARD (NBRS V E x) = 3``;

g `SUC 3 = 4`;
e decide_tac;
val suc_3_4 = top_thm ();

g `SUC 4 = 5`;
e decide_tac;
val suc_4_5 = top_thm ();

g `SUC 5 = 6`;
e decide_tac;
val suc_5_6 = top_thm ();

g `SUC (5 + 3) = 9`;
e decide_tac;
val suc_5_3_9 = top_thm ();

val ramseygraph_3_4_9_3regular = METIS_PROVE [ramseygraph_3_4_9_3regular_lem1,suc_2_3,suc_3_4,suc_5_6,suc_5_3_9,ramsey_2_m_m,ramsey_3_3_6] ``RAMSEYGRAPH 3 4 9 V E ==> x IN V ==> CARD (NBRS V E x) = 3``;

(* -------------------------------------------------------------------------
   Infrastructure to prove the sum of degrees must be odd 
   if there is odd number of vertex with odd degrees.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Sum of degrees must be odd";

g `3 = SUC (2 * 1)`;
e decide_tac;
val eq_3_suc_double_1 = top_thm();

val odd_3 = METIS_PROVE [eq_3_suc_double_1,ODD_DOUBLE] ``ODD 3``;

g `9 = SUC (2 * 4)`;
e decide_tac;
val eq_9_suc_double_4 = top_thm();

val odd_9 = METIS_PROVE [eq_9_suc_double_4,ODD_DOUBLE] ``ODD 9``;

val odd_degr_sum_base = METIS_PROVE [CARD_EMPTY,SUM_IMAGE_THM] ``ODD (CARD EMPTY) <=> ODD (SUM_IMAGE (DEGR V E) EMPTY)``;

val odd_degr_sum_ind_lem1 = METIS_PROVE [INSERT_SUBSET,ODD,ODD_ADD] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (SUC (CARD U)) <=> ODD (DEGR V E v + SUM_IMAGE (DEGR V E) U)))``;

val odd_degr_sum_ind_lem2 = METIS_PROVE [odd_degr_sum_ind_lem1,CARD_INSERT] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (CARD (v INSERT U)) <=> ODD (DEGR V E v + SUM_IMAGE (DEGR V E) U)))``;

val odd_degr_sum_ind_lem3 = METIS_PROVE [odd_degr_sum_ind_lem2,DELETE_NON_ELEMENT] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> !U. FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (CARD (v INSERT U)) <=> ODD (DEGR V E v + SUM_IMAGE (DEGR V E) (U DELETE v))))``;

val odd_degr_sum_ind = METIS_PROVE [odd_degr_sum_ind_lem3,SUM_IMAGE_THM] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> !U. FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (CARD (v INSERT U)) <=> ODD (SUM_IMAGE (DEGR V E) (v INSERT U))))``;

g `(!x. x IN V ==> ODD (DEGR V E x)) ==> !U. FINITE U ==> U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))`;
e DISCH_TAC;
e Induct;
e CONJ_TAC;
e (METIS_TAC [odd_degr_sum_base]);
e (METIS_TAC [odd_degr_sum_ind]);
val odd_degr_sum = top_thm ();

val odd_degr_sum_V = METIS_PROVE [odd_degr_sum,SUBSET_REFL] ``FINITE (V:num -> bool) ==> (!x. x IN V ==> ODD (DEGR V E x)) ==> (ODD (CARD V) <=> ODD (SUM_IMAGE (DEGR V E) V))``;

val ramseygraph_3_4_9_odddegr = METIS_PROVE [ramseygraph_3_4_9_3regular,odd_3,degr_def] ``RAMSEYGRAPH 3 4 9 V E ==> !x.x IN V ==> ODD (DEGR V E x)``;

val ramseygraph_3_4_9_odd_degr_sum = METIS_PROVE [ramseygraph_3_4_9_odddegr,ramseygraph_e1,HAS_SIZE,degr_def,odd_degr_sum_V,odd_9] ``RAMSEYGRAPH 3 4 9 V E ==> ODD (SUM_IMAGE (DEGR V E) V)``;

(* -------------------------------------------------------------------------
   Infrastructure to prove the sum of degrees must be even
   ------------------------------------------------------------------------- *)

val _ = print_endline "Sum of degrees must be even";

g `SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> !x. x IN V ==> NBRS (e INSERT V) E x = NBRS V E x`;
e (rw [nbrs_def,EXTENSION,SPECIFICATION]);
e (METIS_TAC [sym_def]);
val sum_degr_even_lem1 = top_thm ();

g `SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> !x. x IN V ==> DEGR (e INSERT V) E x = DEGR V E x`;
e (rw [degr_def]);
e (IMP_RES_TAC sum_degr_even_lem1);
e (METIS_TAC []);
val sum_degr_even_lem2 = top_thm ();

g `SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> NBRS (e INSERT V) E e = EMPTY`;
e (rw [nbrs_def,EXTENSION,SPECIFICATION]);
e (METIS_TAC []);
val sum_degr_even_lem3 = top_thm ();

g `SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> DEGR (e INSERT V) E e = 0`;
e (rw [degr_def]);
e (IMP_RES_TAC sum_degr_even_lem3);
e (METIS_TAC [CARD_EMPTY]);
val sum_degr_even_lem4 = top_thm ();

g `~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> U SUBSET NBRS V E e`;
e (rw [nbrs_def,EXTENSION,SPECIFICATION,SUBSET_DEF]);
val sum_degr_even_lem5 = top_thm ();

g `~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> ?E'. SYM E' /\ NBRS V E' e = U /\ (!x. x IN V ==> NBRS V E' x = NBRS V E x) /\ e' INSERT NBRS (e INSERT V) E' e = NBRS (e INSERT V) E e /\ (!x. x IN V DELETE e' ==> NBRS (e INSERT V) E' x = NBRS (e INSERT V) E x) /\ NBRS (e INSERT V) E e' = e INSERT NBRS (e INSERT V) E' e' /\ ~(e' IN NBRS (e INSERT V) E' e)`;
e (rw []);
e (ASM_CASES_TAC ``e' IN NBRS V E e``);
e (ASM_CASES_TAC ``e' IN (V:num -> bool)``);
e (qexists_tac `\u v:num. E u v /\ ~(u = e /\ v = e') /\ ~(u = e' /\ v = e)`);
e CONJ_TAC;
e (rw [sym_def]);
e (METIS_TAC [sym_def]);
e CONJ_TAC;
e (UNDISCH_TAC ``NBRS V E e = e' INSERT U``);
e (rw [nbrs_def,EXTENSION,SPECIFICATION]);
e EQ_TAC;
e (METIS_TAC []);
e (METIS_TAC [sym_def,SPECIFICATION]);
e CONJ_TAC;
e (rw [nbrs_def,EXTENSION,SPECIFICATION]);
e (METIS_TAC [sym_def,SPECIFICATION]);
e CONJ_TAC;
e (rw [nbrs_def,EXTENSION,SPECIFICATION,INSERT_DEF]);
e EQ_TAC;
e (rw []);
e (METIS_TAC [nbrs_sub,SUBSET_DEF,SPECIFICATION]);
e (METIS_TAC []);
e (METIS_TAC [nbrs_def,SPECIFICATION]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []); (* 11 *)
e CONJ_TAC;
e GEN_TAC;
e DISCH_TAC;
e (rw [nbrs_def,EXTENSION,SPECIFICATION]);
e EQ_TAC;
e (METIS_TAC []); (* 12 *)
e DISCH_TAC;
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e (METIS_TAC [SPECIFICATION]);
e (rw [nbrs_def,EXTENSION,SPECIFICATION]);
e EQ_TAC;
e (METIS_TAC []);
e DISCH_TAC;
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC [sym_def,nbrs_def,SPECIFICATION]);
e (METIS_TAC [sym_def,nbrs_def,SPECIFICATION]);
e (METIS_TAC [nbrs_def,SPECIFICATION]);
e (UNDISCH_TAC ``~(e' IN NBRS V E e)``);
e (rw []);
val sum_degr_even_lem6 = top_thm ();

g `~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> ?E'. SYM E' /\ NBRS V E' e = U /\ (!x. x IN V ==> NBRS V E' x = NBRS V E x) /\ NBRS (e INSERT V) E e = e' INSERT NBRS (e INSERT V) E' e /\ (!x. x IN V DELETE e' ==> NBRS (e INSERT V) E' x = NBRS (e INSERT V) E x) /\ NBRS (e INSERT V) E e' = e INSERT NBRS (e INSERT V) E' e' /\ ~(e' IN NBRS (e INSERT V) E' e) /\ e' IN NBRS V E e`;
e DISCH_TAC;
e DISCH_TAC;
e DISCH_TAC;
e DISCH_TAC;
e DISCH_TAC;
e (IMP_RES_TAC sum_degr_even_lem6);
e (qexists_tac `E'`);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e (simp []);
val sum_degr_even_lem7 = top_thm ();

g `(!x. x IN V DELETE e' ==> NBRS (e INSERT V) E' x = NBRS (e INSERT V) E x) ==> !x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x`;
e DISCH_TAC;
e GEN_TAC;
e DISCH_TAC;
e (rw [degr_def]);
val sum_degr_even_lem8 = top_thm ();

g `FINITE V ==> NBRS (e INSERT V) E e' = e INSERT NBRS (e INSERT V) E' e' ==> ~(e IN NBRS (e INSERT V) E' e') ==> DEGR (e INSERT V) E e' = SUC (DEGR (e INSERT V) E' e')`;
e DISCH_TAC;
e DISCH_TAC;
e (rw [degr_def]);
e (rw [CARD_INSERT,FINITE_INSERT,nbrs_finite]);
val sum_degr_even_lem9 = top_thm ();


g `~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> ?E'. SYM E' /\ NBRS V E' e = U /\ (!x. x IN V ==> DEGR V E' x = DEGR V E x) /\ SUC (DEGR (e INSERT V) E' e) = DEGR (e INSERT V) E e /\ SUC (∑ (DEGR (e INSERT V) E') V) = ∑ (DEGR (e INSERT V) E) V /\ (!x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x)`;
e (rw []);
e (IMP_RES_TAC sum_degr_even_lem7);
e (qexists_tac `E'`);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (METIS_TAC []);
e CONJ_TAC;
e (rw [degr_def]);
e CONJ_TAC;
e (rw [degr_def]);
e (ASM_CASES_TAC ``FINITE (NBRS (e INSERT V) E' e)``);
e (rw [CARD_INSERT]);
e (METIS_TAC [nbrs_finite,FINITE_INSERT]);
e (ASM_CASES_TAC ``!x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x``);
e CONJ_TAC;
e (ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e' INSERT V DELETE e') = SUC (SUM_IMAGE (DEGR (e INSERT V) E') (e' INSERT V DELETE e'))``);
e (UNDISCH_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e' INSERT V DELETE e') = SUC (SUM_IMAGE (DEGR (e INSERT V) E') (e' INSERT V DELETE e'))``);
e (ASM_CASES_TAC ``(e':num) IN V``);
e (rw [INSERT_DELETE]);
e (METIS_TAC [nbrs_def,SPECIFICATION]);
e (ASM_CASES_TAC ``DEGR (e INSERT V) E e' + SUM_IMAGE (DEGR (e INSERT V) E) (V DELETE e') = SUC (DEGR (e INSERT V) E' e' + ∑ (DEGR (e INSERT V) E') (V DELETE e'))``);
e (ASM_CASES_TAC ``(e':num) IN V DELETE e'``);
e (METIS_TAC [IN_DELETE]);
e (UNDISCH_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e' INSERT V DELETE e') <> SUC (SUM_IMAGE (DEGR (e INSERT V) E') (e' INSERT V DELETE e'))``);
e (rw [SUM_IMAGE_THM]);
e (ASM_CASES_TAC ``DEGR (e INSERT V) E e' + SUM_IMAGE (DEGR (e INSERT V) E) (V DELETE e') = SUC (DEGR (e INSERT V) E' e') + ∑ (DEGR (e INSERT V) E') (V DELETE e')``);
e decide_tac;
e (ASM_CASES_TAC ``DEGR (e INSERT V) E e' = SUC (DEGR (e INSERT V) E' e')``);
e (ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (V DELETE e') = ∑ (DEGR (e INSERT V) E') (V DELETE e')``);
e (METIS_TAC []);
e (METIS_TAC [SUM_IMAGE_CONG]);
e (ASM_CASES_TAC ``e IN NBRS (e INSERT V) E' e'``);
e (ASM_CASES_TAC ``e' IN NBRS (e INSERT V) E' e``);
e (METIS_TAC []);
e (ASM_CASES_TAC ``(e':num) IN e INSERT V``);
e (ASM_CASES_TAC ``(e':num) IN V``);
e (METIS_TAC [nbrs_swap]);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (ASM_CASES_TAC ``(e':num) IN V``);
e (UNDISCH_TAC ``(e':num) IN V``);
e (UNDISCH_TAC ``~((e':num) IN e INSERT V)``);
e (rw []);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC [sum_degr_even_lem9]);
e (UNDISCH_TAC ``!x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x``);
e (rw []);
e (METIS_TAC [sum_degr_even_lem8]);
val sum_degr_even_lem10 = top_thm ();


g `~(e IN V) ==> FINITE V ==> (!x. x IN C ==> DEGR V E' x = DEGR V E x) ==> SUC (DEGR (e INSERT V) E' e) = DEGR (e INSERT V) E e ==> SUC (SUM_IMAGE (DEGR (e INSERT V) E') V) = ∑ (DEGR (e INSERT V) E) V ==> SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = 2 + SUM_IMAGE (DEGR (e INSERT V) E') (e INSERT V)`;
e (rw [SUM_IMAGE_THM,DELETE_NON_ELEMENT]);
val sum_degr_even_lem11 = top_thm ();

g `~(e IN V) ==> FINITE V ==> !U:num -> bool. FINITE U ==> !E:num -> num -> bool. SYM E ==> NBRS V E e = U ==> SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = SUM_IMAGE (DEGR V E) V + 2 * CARD U`;
e DISCH_TAC;
e DISCH_TAC;
e Induct;
e CONJ_TAC;
e GEN_TAC;
e DISCH_TAC;
e DISCH_TAC;
e (rw [SUM_IMAGE_THM]);
e (ASM_CASES_TAC ``V DELETE e = (V:num -> bool)``);
e (IMP_RES_TAC sum_degr_even_lem4);
e (rw []);
e (IMP_RES_TAC sum_degr_even_lem2);
e (METIS_TAC [SUM_IMAGE_CONG]);
e (METIS_TAC [DELETE_NON_ELEMENT]);
e (rw []);
e (IMP_RES_TAC sum_degr_even_lem10);
e (IMP_RES_TAC sum_degr_even_lem11);
e (ASM_CASES_TAC ``NBRS V E' e = (U:num -> bool)``);
e (ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E') (e INSERT V) = 2 * CARD (U:num -> bool) + SUM_IMAGE (DEGR V E') V``);
e (ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = 2 + SUM_IMAGE (DEGR (e INSERT V) E') (e INSERT V)``);
e (ASM_CASES_TAC ``SUM_IMAGE (DEGR V E) V = SUM_IMAGE (DEGR V E') V``);
e (rw []);
e (METIS_TAC [SUM_IMAGE_CONG]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val sum_degr_even_lem12 = top_thm ();

g `~(e IN V) ==> FINITE V ==> SYM E ==> SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = SUM_IMAGE (DEGR V E) V + 2 * CARD (NBRS V E e)`;
e (PROVE_TAC [sum_degr_even_lem12,nbrs_finite]);
val sum_degr_even_lem13 = top_thm ();

g `SYM E ==> !V:num -> bool. FINITE V ==> EVEN (SUM_IMAGE (DEGR V E) V)`;
e DISCH_TAC;
e Induct;
e CONJ_TAC;
e (rw [SUM_IMAGE_THM]);
e (rw []);
e (rw [sum_degr_even_lem13]);
e (METIS_TAC [EVEN_ADD,EVEN_DOUBLE]);
val sum_degr_even = top_thm ();

(* -------------------------------------------------------------------------
   R(3,4) <= 9 (second part)
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,4) <= 9 (second part)";

g `RAMSEY 3 4 9`;
e (rw [ramsey_def]);
e DISCH_TAC;
e (ASM_CASES_TAC ``ODD (SUM_IMAGE (DEGR V E) V)``);
e (ASM_CASES_TAC ``EVEN (SUM_IMAGE (DEGR V E) V)``);
e (METIS_TAC [EVEN_AND_ODD]);
e (METIS_TAC [sum_degr_even,ramseygraph_e1,ramseygraph_e2,HAS_SIZE]);
e (METIS_TAC [ramseygraph_3_4_9_odd_degr_sum]);
val ramsey_3_4_9 = top_thm ();

g `SUC 8 = 9`;
e decide_tac;
val suc_8_9 = top_thm ();

g `RAMSEY (SUC 2) 4 (SUC 8)`;
e (METIS_TAC [ramsey_3_4_9,suc_2_3,suc_8_9]);
val ramsey_S2_4_S8 = top_thm ();

g `RAMSEY (SUC 2) (SUC 4) (SUC (SUC (8 + 4)))`;
e (METIS_TAC [ramsey_sum,ramsey_2_m_m,ramsey_S2_4_S8,suc_3_4]);
val ramsey_S2_S4_SS84 = top_thm ();

(* -------------------------------------------------------------------------
   R(3,5) <= 14
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,5) <= 14";

g `RAMSEY 3 5 14`;
e (ASM_CASES_TAC ``SUC (SUC (8 + 4)) = 14``);
e (METIS_TAC [ramsey_S2_S4_SS84,suc_2_3,suc_4_5]);
e decide_tac;
val ramsey_3_5_14 = top_thm ();

(* -------------------------------------------------------------------------
   R(4,4) <= 18
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(4,4) <= 18";

g `RAMSEY 3 (SUC 3) (SUC 8)`;
e (METIS_TAC [ramsey_3_4_9,suc_3_4,suc_8_9]);
val ramsey_3_S3_S8 = top_thm ();

g `RAMSEY 4 4 18`;
e (ASM_CASES_TAC ``SUC (SUC (8 + 8)) = 18``);
e (METIS_TAC [ramsey_sum,ramsey_3_S3_S8,suc_3_4,ramsey_sym]);
e decide_tac;
val ramsey_4_4_18 = top_thm ();

(* -------------------------------------------------------------------------
   Proving that in a R(4,5,25) there exists a vertex of degree 8,10 or 12
   ------------------------------------------------------------------------- *)

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12";
(* PolyML.print_depth 20; chatting := true; *)
g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x < 14`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (METIS_TAC [ramseygraph_deg_card_bd,ramsey_3_5_14]);
e (METIS_TAC [suc_3_4]);
val ramseygraph_4_5_25_upper_bd = top_thm ();

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12 1";

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> 6 < DEGR V E x`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) (SUC 24) V E``);
e (ASM_CASES_TAC ``24 < CARD (NBRS V E x) + 18``);
e decide_tac;
e (METIS_TAC [ramseygraph_deg_card_lower_bd,ramsey_4_4_18]);
e (ASM_CASES_TAC ``SUC 24 = 25``);
e (METIS_TAC [suc_4_5]);
e decide_tac;
val ramseygraph_4_5_25_lower_bd = top_thm ();

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12 2";

g `ODD 25`;
e (ASM_CASES_TAC ``25 = SUC (2 * 12)``);
e (METIS_TAC [ODD_DOUBLE]);
e decide_tac;
val odd_25 = top_thm ();

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12 3";

g `RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ EVEN (DEGR V E x)`;
e (rw []);
e CCONTR_TAC;
e (ASM_CASES_TAC ``!x. x IN V ==> ODD (DEGR V E x)``);
e (ASM_CASES_TAC ``ODD (SUM_IMAGE (DEGR V E) V)``);
e (ASM_CASES_TAC ``EVEN (SUM_IMAGE (DEGR V E) V)``);
e (METIS_TAC [EVEN_AND_ODD]);
e (METIS_TAC [sum_degr_even,ramseygraph_e1,ramseygraph_e2,HAS_SIZE]);
e (METIS_TAC [odd_degr_sum_V,ramseygraph_e1,HAS_SIZE,odd_25]);
e (METIS_TAC [ODD_EVEN]);
val ramseygraph_4_5_25_ex_even = top_thm ();

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12 4";

g `6 < n ==> n < 14 ==> EVEN n ==> n = 8 \/ n = 10 \/ n = 12`;
e ((rw_tac numLib.arith_ss) [] >> pop_assum (Q.X_CHOOSE_THEN `m` SUBST_ALL_TAC o REWRITE_RULE [EVEN_EXISTS, TIMES2]) >> rw_tac numLib.arith_ss []);
val evens_between_6_14_are_8_10_12 = top_thm ();

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12 5";

g `RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ (DEGR V E x = 8 \/ DEGR V E x = 10 \/ DEGR V E x = 12)`;
e (rw []);
e (IMP_RES_TAC ramseygraph_4_5_25_ex_even);
e (IMP_RES_TAC ramseygraph_4_5_25_lower_bd);
e (IMP_RES_TAC ramseygraph_4_5_25_upper_bd);
e (qexists_tac `x`);
e CONJ_TAC;
e (METIS_TAC []);
e (METIS_TAC [evens_between_6_14_are_8_10_12]);
val ramseygraph_4_5_25_ex_8_10_12 = top_thm ();

(* -------------------------------------------------------------------------
   Degree 8: connection with the first-order formulation used in
   the computational parts of the proof.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Degree 8";

g `8 + 16 = 24`;
e decide_tac;
val add_8_16 = top_thm ();

g `x = 8 ==> y <> 16 ==> x + y = 24 ==> F`;
e decide_tac;
val add_8_16_alt = top_thm ();

g `SUC 24 = 25`;
e decide_tac;
val suc_24_25 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> RAMSEYGRAPH 3 5 8 (NBRS V E x) E`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (ASM_CASES_TAC ``HAS_DEG V E x 8``);
e (METIS_TAC [ramseygraph_nbrs]);
e (METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite]);
e (METIS_TAC [suc_3_4]);
val r4525_no8_lem1 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> RAMSEYGRAPH 4 4 16 (ANTINBRS V E x) E`;
e (rw []);
e (IMP_RES_TAC r4525_no8_lem1);
e (UNDISCH_TAC ``DEGR V E x = 8``);
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E``);
e (ASM_CASES_TAC ``HAS_ANTIDEG V E x 16``);
e (METIS_TAC [ramseygraph_antinbrs]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E``);
e (IMP_RES_TAC deg_antideg_sum_card);
e (METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_8_16_alt]);
e (METIS_TAC [suc_24_25]);
e (METIS_TAC [suc_4_5]);
val r4525_no8_lem2 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 8 ==> h i IN NBRS V E x) /\ (!j. 8 <= j ==> j < 24 ==> h j IN ANTINBRS V E x)`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (ASM_CASES_TAC ``HAS_DEG V E x 8``);
e (IMP_RES_TAC ramseygraph_nbrs);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E``);
e (ASM_CASES_TAC ``HAS_ANTIDEG V E x 16``);
e (IMP_RES_TAC ramseygraph_antinbrs);
e (ASM_CASES_TAC ``(NBRS V E x) HAS_SIZE 8``);
e (ASM_CASES_TAC ``(ANTINBRS V E x) HAS_SIZE 16``);
e (IMP_RES_TAC has_size_bij);
e (ASM_CASES_TAC ``NBRS V E x INTER ANTINBRS V E x = EMPTY``);
e (METIS_TAC [combine_count_bijs,add_8_16]);
e (METIS_TAC [nbrs_antinbrs_inter]);
e (METIS_TAC [HAS_SIZE,hasantideg_def]);
e (METIS_TAC [HAS_SIZE,hasdeg_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E``);
e (IMP_RES_TAC deg_antideg_sum_card);
e (METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_8_16_alt]);
e (METIS_TAC [suc_24_25]);
e (METIS_TAC [suc_4_5]);
e (METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite]);
e (METIS_TAC [suc_3_4]);
val r4525_no8_lem3 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 8 ==> h i IN NBRS V E x) /\ (!j. 8 <= j ==> j < 24 ==> h j IN ANTINBRS V E x) /\ INJ h (count 8) (NBRS V E x) /\ INJ (\i.h (i + 8)) (count 16) (ANTINBRS V E x)`;
e (rw []);
e (IMP_RES_TAC r4525_no8_lem3);
e (qexists_tac `(h:num -> num)`);
e (UNDISCH_TAC ``BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x)``);
e (rw [BIJ_DEF,INJ_DEF]);
e (ASM_CASES_TAC ``i + 8 = i' + 8``);
e decide_tac;
e (ASM_CASES_TAC ``i + 8 < 24``);
e (ASM_CASES_TAC ``i' + 8 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
val r4525_no8_lem4 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> ?E':num -> num -> bool. (!x y. E' x y <=> E' y x) /\ RAMSEYGRAPH 4 5 24 (count 24) E' /\ RAMSEYGRAPH 3 5 8 (count 8) E' /\ RAMSEYGRAPH 4 4 16 (count 16) (\i j.E' (i + 8) (j + 8))`;
e (rw []);
e (IMP_RES_TAC r4525_no8_lem1);
e (IMP_RES_TAC r4525_no8_lem2);
e (IMP_RES_TAC r4525_no8_lem4);
e (qexists_tac `\i j.E (h i) (h j)`);
e BETA_TAC;
e CONJ_TAC;
e (METIS_TAC [ramseygraph_def,sym_def]);
e CONJ_TAC;
e (UNDISCH_TAC ``RAMSEYGRAPH 4 5 25 V E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 24``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASCLIQUE 4 V E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 24``);
e (ASM_CASES_TAC ``x'' < 8``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x``);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e (ASM_CASES_TAC ``8 <= x''``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x``);
e (METIS_TAC [antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size,BIJ_DEF]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 24``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASANTICLIQUE 5 V E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 24``);
e (ASM_CASES_TAC ``x'' < 8``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x``);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e (ASM_CASES_TAC ``8 <= x''``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x``);
e (METIS_TAC [antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size,BIJ_DEF]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CONJ_TAC;
e (UNDISCH_TAC ``RAMSEYGRAPH 3 5 8 (NBRS V E x) E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 8``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 3``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASCLIQUE 3 (NBRS V E x) E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 8``);
e (METIS_TAC []);
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 8``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (NBRS V E x) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 8``);
e (METIS_TAC []);
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (UNDISCH_TAC ``RAMSEYGRAPH 4 4 16 (ANTINBRS V E x) E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 16``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h (i + 8)):num) (h (j + 8))``);
e (UNDISCH_TAC ``~HASCLIQUE 4 (ANTINBRS V E x) E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE (\i.h (i + 8)) (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``i < 16``);
e (ASM_CASES_TAC ``8 <= i + 8``);
e (ASM_CASES_TAC ``i + 8 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 16``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h (i + 8)):num) (h (j + 8))``);
e (UNDISCH_TAC ``~HASANTICLIQUE 4 (ANTINBRS V E x) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE (\i.h (i + 8)) (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``i < 16``);
e (ASM_CASES_TAC ``8 <= i + 8``);
e (ASM_CASES_TAC ``i + 8 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4525_no8_lem5 = top_thm ();

g `RAMSEYGRAPH 4 4 16 (count 16) E ==> C4416b E /\ C4416r E`;
e (rw [ramseygraph_def,sym_def,c4416b_def,c4416r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 4 (count 16) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 4 (count 16) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4416_c4416_thm = top_thm ();

g `RAMSEYGRAPH 3 5 8 (count 8) E ==> C358b E /\ C358r E`;
e (rw [ramseygraph_def,sym_def,c358b_def,c358r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 3 (count 8) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (count 8) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3; x4}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r358_c358_thm = top_thm ();

g `RAMSEYGRAPH 4 5 24 (count 24) E ==> C4524b E /\ C4524r E`;
e (rw [ramseygraph_def,sym_def,c4524b_def,c4524r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 4 (count 24) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (count 24) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3; x4}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4524_c4524_thm = top_thm ();

g `HASCLIQUE 4 V E ==> ?x0 x1 x2 x3:num. x0 IN V /\ x1 IN V /\ x2 IN V /\ x3 IN V /\ x0 <> x1 /\ x0 <> x2 /\ x0 <> x3 /\ x1 <> x2 /\ x1 <> x3 /\ x2 <> x3 /\ E x0 x1 /\ E x0 x2 /\ E x0 x3 /\ E x1 x2 /\ E x1 x3 /\ E x2 x3`;
e (rw [hasclique_def]);
e (IMP_RES_TAC has_size_bij);
e (qexists_tac `f 0`);
e (qexists_tac `f 1`);
e (qexists_tac `f 2`);
e (qexists_tac `f 3`);
e (ASM_CASES_TAC ``0 < 4``);
e (ASM_CASES_TAC ``1 < 4``);
e (ASM_CASES_TAC ``2 < 4``);
e (ASM_CASES_TAC ``3 < 4``);
e (IMP_RES_TAC bij_count_in);
e (ASM_CASES_TAC ``0 = 1``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 1``);
e decide_tac;
e (ASM_CASES_TAC ``0 = 2``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 2``);
e decide_tac;
e (ASM_CASES_TAC ``0 = 3``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 3``);
e decide_tac;
e (ASM_CASES_TAC ``1 = 2``);
e CCONTR_TAC;
e (UNDISCH_TAC ``1 = 2``);
e decide_tac;
e (ASM_CASES_TAC ``1 = 3``);
e CCONTR_TAC;
e (UNDISCH_TAC ``1 = 3``);
e decide_tac;
e (ASM_CASES_TAC ``2 = 3``);
e CCONTR_TAC;
e (UNDISCH_TAC ``2 = 3``);
e decide_tac;
e (IMP_RES_TAC bij_count_neq);
e (METIS_TAC [SUBSET_DEF]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~(3 < 4)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(2 < 4)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(1 < 4)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(0 < 4)``);
e decide_tac;
val hasclique_4_e = top_thm ();

g `HASANTICLIQUE 5 V E ==> ?x0 x1 x2 x3 x4:num. x0 IN V /\ x1 IN V /\ x2 IN V /\ x3 IN V /\ x4 IN V /\ x0 <> x1 /\ x0 <> x2 /\ x0 <> x3 /\ x0 <> x4 /\ x1 <> x2 /\ x1 <> x3 /\ x1 <> x4 /\ x2 <> x3 /\ x2 <> x4 /\ x3 <> x4 /\ ~E x0 x1 /\ ~E x0 x2 /\ ~E x0 x3 /\ ~E x0 x4 /\ ~E x1 x2 /\ ~E x1 x3 /\ ~E x1 x4 /\ ~E x2 x3 /\ ~E x2 x4 /\ ~E x3 x4`;
e (rw [hasanticlique_def,hasclique_def]);
e (IMP_RES_TAC has_size_bij);
e (qexists_tac `f 0`);
e (qexists_tac `f 1`);
e (qexists_tac `f 2`);
e (qexists_tac `f 3`);
e (qexists_tac `f 4`);
e (ASM_CASES_TAC ``0 < 5``);
e (ASM_CASES_TAC ``1 < 5``);
e (ASM_CASES_TAC ``2 < 5``);
e (ASM_CASES_TAC ``3 < 5``);
e (ASM_CASES_TAC ``4 < 5``);
e (IMP_RES_TAC bij_count_in);
e (ASM_CASES_TAC ``0 = 1``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 1``);
e decide_tac;
e (ASM_CASES_TAC ``0 = 2``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 2``);
e decide_tac;
e (ASM_CASES_TAC ``0 = 3``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 3``);
e decide_tac;
e (ASM_CASES_TAC ``0 = 4``);
e CCONTR_TAC;
e (UNDISCH_TAC ``0 = 4``);
e decide_tac;
e (ASM_CASES_TAC ``1 = 2``);
e CCONTR_TAC;
e (UNDISCH_TAC ``1 = 2``);
e decide_tac;
e (ASM_CASES_TAC ``1 = 3``);
e CCONTR_TAC;
e (UNDISCH_TAC ``1 = 3``);
e decide_tac;
e (ASM_CASES_TAC ``1 = 4``);
e CCONTR_TAC;
e (UNDISCH_TAC ``1 = 4``);
e decide_tac;
e (ASM_CASES_TAC ``2 = 3``);
e CCONTR_TAC;
e (UNDISCH_TAC ``2 = 3``);
e decide_tac;
e (ASM_CASES_TAC ``2 = 4``);
e CCONTR_TAC;
e (UNDISCH_TAC ``2 = 4``);
e decide_tac;
e (ASM_CASES_TAC ``3 = 4``);
e CCONTR_TAC;
e (UNDISCH_TAC ``3 = 4``);
e decide_tac;
e (IMP_RES_TAC bij_count_neq);
e (METIS_TAC [SUBSET_DEF]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~(4 < 5)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(3 < 5)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(2 < 5)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(1 < 5)``);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~(0 < 5)``);
e decide_tac;
val hasanticlique_5_e = top_thm ();

g `SYM E ==> C4524b E /\ C4524r E ==> RAMSEYGRAPH 4 5 24 (count 24) E`;
e (rw [ramseygraph_def,sym_def,c4524b_def,c4524r_def]);
e (METIS_TAC [HAS_SIZE,FINITE_COUNT,CARD_COUNT]);
e DISCH_TAC;
e (IMP_RES_TAC hasclique_4_e);
e (ASM_CASES_TAC ``x0 < 24``);
e (ASM_CASES_TAC ``x1 < 24``);
e (ASM_CASES_TAC ``x2 < 24``);
e (ASM_CASES_TAC ``x3 < 24``);
e (PROVE_TAC []);
e (UNDISCH_TAC ``x3 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x2 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x1 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x0 IN count 24``);
e (simp []);
e DISCH_TAC;
e (IMP_RES_TAC hasanticlique_5_e);
e (ASM_CASES_TAC ``x0 < 24``);
e (ASM_CASES_TAC ``x1 < 24``);
e (ASM_CASES_TAC ``x2 < 24``);
e (ASM_CASES_TAC ``x3 < 24``);
e (ASM_CASES_TAC ``x4 < 24``);
e (PROVE_TAC []);
e (UNDISCH_TAC ``x4 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x3 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x2 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x1 IN count 24``);
e (simp []);
e (UNDISCH_TAC ``x0 IN count 24``);
e (simp []);
val c4524_r4524_thm = top_thm ();

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> F`;
e (rw []);
e DISCH_TAC;
e (IMP_RES_TAC r4525_no8_lem5);
e (IMP_RES_TAC r358_c358_thm);
e (IMP_RES_TAC r4416_c4416_thm);
e (IMP_RES_TAC r4524_c4524_thm);
e (METIS_TAC []);
val r4525_no_deg8 = top_thm ();

(* -------------------------------------------------------------------------
   Degree 10: connection with the first-order formulation used in
   the computational parts of the proof.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Degree 10";

g `10 + 14 = 24`;
e decide_tac;
val add_10_14 = top_thm ();

g `x = 10 ==> y <> 14 ==> x + y = 24 ==> F`;
e decide_tac;
val add_10_14_alt = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> RAMSEYGRAPH 3 5 10 (NBRS V E x) E`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (ASM_CASES_TAC ``HAS_DEG V E x 10``);
e (METIS_TAC [ramseygraph_nbrs]);
e (METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite]);
e (METIS_TAC [suc_3_4]);
val r4525_no10_lem1 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> RAMSEYGRAPH 4 4 14 (ANTINBRS V E x) E`;
e (rw []);
e (IMP_RES_TAC r4525_no10_lem1);
e (UNDISCH_TAC ``DEGR V E x = 10``);
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E``);
e (ASM_CASES_TAC ``HAS_ANTIDEG V E x 14``);
e (METIS_TAC [ramseygraph_antinbrs]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E``);
e (IMP_RES_TAC deg_antideg_sum_card);
e (METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_10_14_alt]);
e (METIS_TAC [suc_24_25]);
e (METIS_TAC [suc_4_5]);
val r4525_no10_lem2 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 10 ==> h i IN NBRS V E x) /\ (!j. 10 <= j ==> j < 24 ==> h j IN ANTINBRS V E x)`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (ASM_CASES_TAC ``HAS_DEG V E x 10``);
e (IMP_RES_TAC ramseygraph_nbrs);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E``);
e (ASM_CASES_TAC ``HAS_ANTIDEG V E x 14``);
e (IMP_RES_TAC ramseygraph_antinbrs);
e (ASM_CASES_TAC ``(NBRS V E x) HAS_SIZE 10``);
e (ASM_CASES_TAC ``(ANTINBRS V E x) HAS_SIZE 14``);
e (IMP_RES_TAC has_size_bij);
e (ASM_CASES_TAC ``NBRS V E x INTER ANTINBRS V E x = EMPTY``);
e (METIS_TAC [combine_count_bijs,add_10_14]);
e (METIS_TAC [nbrs_antinbrs_inter]);
e (METIS_TAC [HAS_SIZE,hasantideg_def]);
e (METIS_TAC [HAS_SIZE,hasdeg_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E``);
e (IMP_RES_TAC deg_antideg_sum_card);
e (METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_10_14_alt]);
e (METIS_TAC [suc_24_25]);
e (METIS_TAC [suc_4_5]);
e (METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite]);
e (METIS_TAC [suc_3_4]);
val r4525_no10_lem3 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 10 ==> h i IN NBRS V E x) /\ (!j. 10 <= j ==> j < 24 ==> h j IN ANTINBRS V E x) /\ INJ h (count 10) (NBRS V E x) /\ INJ (\i.h (i + 10)) (count 14) (ANTINBRS V E x)`;
e (rw []);
e (IMP_RES_TAC r4525_no10_lem3);
e (qexists_tac `(h:num -> num)`);
e (UNDISCH_TAC ``BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x)``);
e (rw [BIJ_DEF,INJ_DEF]);
e (ASM_CASES_TAC ``i + 10 = i' + 10``);
e decide_tac;
e (ASM_CASES_TAC ``i + 10 < 24``);
e (ASM_CASES_TAC ``i' + 10 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
val r4525_no10_lem4 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> ?E':num -> num -> bool. (!x y. E' x y <=> E' y x) /\ RAMSEYGRAPH 4 5 24 (count 24) E' /\ RAMSEYGRAPH 3 5 10 (count 10) E' /\ RAMSEYGRAPH 4 4 14 (count 14) (\i j.E' (i + 10) (j + 10))`;
e (rw []);
e (IMP_RES_TAC r4525_no10_lem1);
e (IMP_RES_TAC r4525_no10_lem2);
e (IMP_RES_TAC r4525_no10_lem4);
e (qexists_tac `\i j.E (h i) (h j)`);
e BETA_TAC;
e CONJ_TAC;
e (METIS_TAC [ramseygraph_def,sym_def]);
e CONJ_TAC;
e (UNDISCH_TAC ``RAMSEYGRAPH 4 5 25 V E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 24``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASCLIQUE 4 V E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 24``);
e (ASM_CASES_TAC ``x'' < 10``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x``);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e (ASM_CASES_TAC ``10 <= x''``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x``);
e (METIS_TAC [antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size,BIJ_DEF]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 24``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASANTICLIQUE 5 V E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 24``);
e (ASM_CASES_TAC ``x'' < 10``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x``);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e (ASM_CASES_TAC ``10 <= x''``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x``);
e (METIS_TAC [antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size,BIJ_DEF]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CONJ_TAC;
e (UNDISCH_TAC ``RAMSEYGRAPH 3 5 10 (NBRS V E x) E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 10``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 3``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASCLIQUE 3 (NBRS V E x) E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 10``);
e (METIS_TAC []);
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 10``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (NBRS V E x) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 10``);
e (METIS_TAC []);
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (UNDISCH_TAC ``RAMSEYGRAPH 4 4 14 (ANTINBRS V E x) E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 14``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h (i + 10)):num) (h (j + 10))``);
e (UNDISCH_TAC ``~HASCLIQUE 4 (ANTINBRS V E x) E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE (\i.h (i + 10)) (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``i < 14``);
e (ASM_CASES_TAC ``10 <= i + 10``);
e (ASM_CASES_TAC ``i + 10 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 14``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h (i + 10)):num) (h (j + 10))``);
e (UNDISCH_TAC ``~HASANTICLIQUE 4 (ANTINBRS V E x) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE (\i.h (i + 10)) (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``i < 14``);
e (ASM_CASES_TAC ``10 <= i + 10``);
e (ASM_CASES_TAC ``i + 10 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4525_no10_lem5 = top_thm ();



g `RAMSEYGRAPH 4 4 14 (count 14) E ==> C4414b E /\ C4414r E`;
e (rw [ramseygraph_def,sym_def,c4414b_def,c4414r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 4 (count 14) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 4 (count 14) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4414_c4414_thm = top_thm ();

g `RAMSEYGRAPH 3 5 10 (count 10) E ==> C3510b E /\ C3510r E`;
e (rw [ramseygraph_def,sym_def,c3510b_def,c3510r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 3 (count 10) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (count 10) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3; x4}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r3510_c3510_thm = top_thm ();

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> F`;
e (rw []);
e DISCH_TAC;
e (IMP_RES_TAC r4525_no10_lem5);
e (IMP_RES_TAC r3510_c3510_thm);
e (IMP_RES_TAC r4414_c4414_thm);
e (IMP_RES_TAC r4524_c4524_thm);
e (METIS_TAC []);
val r4525_no_deg10 = top_thm ();

(* -------------------------------------------------------------------------
   Degree 12: connection with the first-order formulation used in
   the computational parts of the proof.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Degree 12";

g `12 + 12 = 24`;
e decide_tac;
val add_12_12 = top_thm ();

g `x = 12 ==> y <> 12 ==> x + y = 24 ==> F`;
e decide_tac;
val add_12_12_alt = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> RAMSEYGRAPH 3 5 12 (NBRS V E x) E`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (ASM_CASES_TAC ``HAS_DEG V E x 12``);
e (METIS_TAC [ramseygraph_nbrs]);
e (METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite]);
e (METIS_TAC [suc_3_4]);
val r4525_no12_lem1 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> RAMSEYGRAPH 4 4 12 (ANTINBRS V E x) E`;
e (rw []);
e (IMP_RES_TAC r4525_no12_lem1);
e (UNDISCH_TAC ``DEGR V E x = 12``);
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E``);
e (ASM_CASES_TAC ``HAS_ANTIDEG V E x 12``);
e (METIS_TAC [ramseygraph_antinbrs]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E``);
e (IMP_RES_TAC deg_antideg_sum_card);
e (METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_12_12_alt]);
e (METIS_TAC [suc_24_25]);
e (METIS_TAC [suc_4_5]);
val r4525_no12_lem2 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 12 ==> h i IN NBRS V E x) /\ (!j. 12 <= j ==> j < 24 ==> h j IN ANTINBRS V E x)`;
e (rw [degr_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E``);
e (ASM_CASES_TAC ``HAS_DEG V E x 12``);
e (IMP_RES_TAC ramseygraph_nbrs);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E``);
e (ASM_CASES_TAC ``HAS_ANTIDEG V E x 12``);
e (IMP_RES_TAC ramseygraph_antinbrs);
e (ASM_CASES_TAC ``(NBRS V E x) HAS_SIZE 12``);
e (ASM_CASES_TAC ``(ANTINBRS V E x) HAS_SIZE 12``);
e (IMP_RES_TAC has_size_bij);
e (ASM_CASES_TAC ``NBRS V E x INTER ANTINBRS V E x = EMPTY``);
e (METIS_TAC [combine_count_bijs,add_12_12]);
e (METIS_TAC [nbrs_antinbrs_inter]);
e (METIS_TAC [HAS_SIZE,hasantideg_def]);
e (METIS_TAC [HAS_SIZE,hasdeg_def]);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E``);
e (IMP_RES_TAC deg_antideg_sum_card);
e (METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_12_12_alt]);
e (METIS_TAC [suc_24_25]);
e (METIS_TAC [suc_4_5]);
e (METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite]);
e (METIS_TAC [suc_3_4]);
val r4525_no12_lem3 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 12 ==> h i IN NBRS V E x) /\ (!j. 12 <= j ==> j < 24 ==> h j IN ANTINBRS V E x) /\ INJ h (count 12) (NBRS V E x) /\ INJ (\i.h (i + 12)) (count 12) (ANTINBRS V E x)`;
e (rw []);
e (IMP_RES_TAC r4525_no12_lem3);
e (qexists_tac `(h:num -> num)`);
e (UNDISCH_TAC ``BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x)``);
e (rw [BIJ_DEF,INJ_DEF]);
e (ASM_CASES_TAC ``i + 12 = i' + 12``);
e decide_tac;
e (ASM_CASES_TAC ``i + 12 < 24``);
e (ASM_CASES_TAC ``i' + 12 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
val r4525_no12_lem4 = top_thm ();

g `RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> ?E':num -> num -> bool. (!x y. E' x y <=> E' y x) /\ RAMSEYGRAPH 4 5 24 (count 24) E' /\ RAMSEYGRAPH 3 5 12 (count 12) E' /\ RAMSEYGRAPH 4 4 12 (count 12) (\i j.E' (i + 12) (j + 12))`;
e (rw []);
e (IMP_RES_TAC r4525_no12_lem1);
e (IMP_RES_TAC r4525_no12_lem2);
e (IMP_RES_TAC r4525_no12_lem4);
e (qexists_tac `\i j.E (h i) (h j)`);
e BETA_TAC;
e CONJ_TAC;
e (METIS_TAC [ramseygraph_def,sym_def]);
e CONJ_TAC;
e (UNDISCH_TAC ``RAMSEYGRAPH 4 5 25 V E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 24``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASCLIQUE 4 V E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 24``);
e (ASM_CASES_TAC ``x'' < 12``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x``);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e (ASM_CASES_TAC ``12 <= x''``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x``);
e (METIS_TAC [antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size,BIJ_DEF]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 24``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASANTICLIQUE 5 V E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 24``);
e (ASM_CASES_TAC ``x'' < 12``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x``);
e (METIS_TAC [nbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e (ASM_CASES_TAC ``12 <= x''``);
e (ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x``);
e (METIS_TAC [antinbrs_sub,SUBSET_DEF]);
e (METIS_TAC []);
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size,BIJ_DEF]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CONJ_TAC;
e (UNDISCH_TAC ``RAMSEYGRAPH 3 5 12 (NBRS V E x) E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 12``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 3``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASCLIQUE 3 (NBRS V E x) E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 12``);
e (METIS_TAC []);
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 12``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)``);
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (NBRS V E x) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE h (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``x'' < 12``);
e (METIS_TAC []);
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (UNDISCH_TAC ``RAMSEYGRAPH 4 4 12 (ANTINBRS V E x) E``);
e (rw [ramseygraph_def]);
e (METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE]);
e (UNDISCH_TAC ``SYM E``);
e (rw [sym_def]);
e (rw [hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 12``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h (i + 12)):num) (h (j + 12))``);
e (UNDISCH_TAC ``~HASCLIQUE 4 (ANTINBRS V E x) E``);
e (rw [hasclique_def]);
e (qexists_tac `IMAGE (\i.h (i + 12)) (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``i < 12``);
e (ASM_CASES_TAC ``12 <= i + 12``);
e (ASM_CASES_TAC ``i + 12 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [BIJ_DEF,INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (rw [hasanticlique_def,hasclique_def]);
e CCONTR_TAC;
e (ASM_CASES_TAC ``U SUBSET count 12``);
e (ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4``);
e (ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h (i + 12)):num) (h (j + 12))``);
e (UNDISCH_TAC ``~HASANTICLIQUE 4 (ANTINBRS V E x) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `IMAGE (\i.h (i + 12)) (U:num -> bool)`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e (ASM_CASES_TAC ``i < 12``);
e (ASM_CASES_TAC ``12 <= i + 12``);
e (ASM_CASES_TAC ``i + 12 < 24``);
e (METIS_TAC []);
e decide_tac;
e decide_tac;
e (METIS_TAC [SUBSET_DEF,IN_COUNT]);
e CONJ_TAC;
e (METIS_TAC [inj_image_sub_has_size]);
e (rw [IMAGE_DEF,GSPECIFICATION]);
e (METIS_TAC [INJ_DEF]);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4525_no12_lem5 = top_thm ();

(* -------------------------------------------------------------------------
   Connecting with the representations use in the other part of the proof.
   ------------------------------------------------------------------------- *)

g `RAMSEYGRAPH 4 4 12 (count 12) E ==> C4412b E /\ C4412r E`;
e (rw [ramseygraph_def,sym_def,c4412b_def,c4412r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 4 (count 12) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 4 (count 12) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r4412_c4412_thm = top_thm ();

g `RAMSEYGRAPH 3 5 12 (count 12) E ==> C3512b E /\ C3512r E`;
e (rw [ramseygraph_def,sym_def,c3512b_def,c3512r_def]);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASCLIQUE 3 (count 12) E``);
e (rw [hasclique_def]);
e (qexists_tac `{x0; x1; x2}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~HASANTICLIQUE 5 (count 12) E``);
e (rw [hasanticlique_def,hasclique_def]);
e (qexists_tac `{x0; x1; x2; x3; x4}`);
e CONJ_TAC;
e (rw [SUBSET_DEF]);
e CONJ_TAC;
e (rw [HAS_SIZE]);
e (rw []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
e (METIS_TAC []);
val r3512_c3512_thm = top_thm ();

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> F`;
e (rw []);
e DISCH_TAC;
e (IMP_RES_TAC r4525_no12_lem5);
e (IMP_RES_TAC r3512_c3512_thm);
e (IMP_RES_TAC r4412_c4412_thm);
e (IMP_RES_TAC r4524_c4524_thm);
e (METIS_TAC []);
val r4525_no_deg12 = top_thm ();

(* -------------------------------------------------------------------------
   Final theorem, if there is no vertex of degree 8,10 or 12
   and R(4,5) > 24, then we have R(4,5) = 25
   ------------------------------------------------------------------------- *)

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ (DEGR V E x = 10 \/ DEGR V E x = 12)`;
e (METIS_TAC [ramseygraph_4_5_25_ex_8_10_12,r4525_no_deg8]);
val ramseygraph_4_5_25_ex_10_12_hyp = top_thm ();

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ DEGR V E x = 12`;
e (METIS_TAC [ramseygraph_4_5_25_ex_10_12_hyp,r4525_no_deg10]);
val ramseygraph_4_5_25_ex_12_hyp = top_thm ();

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> ~RAMSEYGRAPH 4 5 25 V E`;
e DISCH_TAC;
e (IMP_RES_TAC ramseygraph_4_5_25_ex_12_hyp);
e (METIS_TAC [r4525_no_deg12]);
val no_ramseygraph_4_5_25_hyp = top_thm ();

g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEY 4 5 25`;
e (rw [ramsey_def]);
e (METIS_TAC [no_ramseygraph_4_5_25_hyp]);
val ramsey_4_5_25_hyp1 = top_thm ();


g `(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> (?E:num -> num -> bool . SYM E /\ C4524b E /\ C4524r E) ==> RAMS 4 5 = 25`;
e DISCH_TAC;
e DISCH_TAC;
e DISCH_TAC;
e (IMP_RES_TAC ramsey_4_5_25_hyp1);
e (rw []);
e (ASM_CASES_TAC ``RAMSEY 4 5 24``);
e (ASM_CASES_TAC ``RAMSEYGRAPH 4 5 24 (count 24) E``);
e CCONTR_TAC;
e (UNDISCH_TAC ``RAMSEY 4 5 24``);
e (rw [ramsey_def]);
e (qexists_tac `(count 24)`);
e (qexists_tac `E:num->num->bool`);
e (METIS_TAC []);
e CCONTR_TAC;
e (UNDISCH_TAC ``~RAMSEYGRAPH 4 5 24 (count 24) E``);
e (simp []);
e (METIS_TAC [c4524_r4524_thm]);
e (ASM_CASES_TAC ``RAMSEY 4 5 (SUC 24)``);
e (IMP_RES_TAC rams_eq_S);
e decide_tac;
e CCONTR_TAC;
e (UNDISCH_TAC ``~RAMSEY 4 5 (SUC 24)``);
e (simp []);

val ramsey_4_5_25_hyp = 
  save_thm ("ramsey_4_5_25_hyp", UNDISCH_ALL (top_thm ()));

val _ = export_theory ();

