(* =========================================================================
   Upper bound for small ramsey numbers.
   Existence of a vertex of degree d in {8,10,12}. 
   Connection with first-order formulation.
   Sufficient conditions (including existence of a
   R(4,5,24) graph) for proving R(4,5)=25. 
   ========================================================================= *)

(* load "graph"; load "../def/ramseyDefTheory"; *)
open HolKernel boolLib Parse simpLib boolSimps BasicProvers bossLib;
open arithmeticTheory pred_setTheory aiLib kernel graph;
local open numTheory prim_recTheory SatisfySimps DefnBase ramseyDefTheory 
in end;

val _ = new_theory "basicRamsey";

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

val nbrs_swap = TAC_PROOF (
  ``SYM E ==> y IN V ==> x IN NBRS V E y ==> y IN NBRS V E x``,
  METIS_TAC [sym_def,nbrs_def,SPECIFICATION]);

val in_count = TAC_PROOF (``x < n <=> x IN count n``, simp []);

val sing_subset = METIS_PROVE [SUBSET_DEF,IN_SING] ``(x:num) IN V ==> {x} SUBSET V``;
val has_size_1 = METIS_PROVE [HAS_SIZE,SING,SING_IFF_CARD1] ``{(x:num)} HAS_SIZE 1``;

val has_size_insert = TAC_PROOF (
  ``(U:num -> bool) HAS_SIZE n ==> ~(x IN U) ==> x INSERT U HAS_SIZE SUC n``,
  rw [HAS_SIZE,CARD_DEF]);

val suc_1_2 = TAC_PROOF (``SUC 1 = 2``, decide_tac);

val not_in_sing = TAC_PROOF (``(x:num) <> y ==> ~(x IN {y})``, simp []);

val has_size_2 = METIS_PROVE [not_in_sing,has_size_1,has_size_insert,suc_1_2] ``(x:num) <> y ==> {x; y} HAS_SIZE 2``;

val upair_subset = METIS_PROVE [SUBSET_DEF,UNION_SUBSET,INSERT_SING_UNION,sing_subset] ``(x:num) IN V ==> y IN V ==> {x;y} SUBSET V``;

val upair_e = METIS_PROVE [UNION_SUBSET,INSERT_SING_UNION,IN_SING,IN_UNION] ``(u:num) IN {x; y} ==> u = x \/ u = y``;

val has2clique_i_lem1 = METIS_PROVE [sym_def,upair_e] ``SYM E ==> E x y ==> x' IN {x; y} ==> y' IN {x; y} ==> x' <> y' ==> E x' y'``;

val has2clique_i_lem2 = METIS_PROVE [has_size_2,upair_subset,has2clique_i_lem1] ``SYM E ==> (x:num) IN V ==> y IN V ==> x <> y ==> E x y ==> ({x;y} SUBSET V /\ {x;y} HAS_SIZE 2 /\ (!x':num. !y':num . x' IN {x;y} ==> y' IN {x;y} ==> x' <> y' ==> E x' y'))``;

val has2clique_i = TAC_PROOF (
  ``SYM E ==> (x:num) IN V ==> y IN V ==> x <> y ==> E x y ==> HASCLIQUE 2 V E``,
  rw [hasclique_def] >- qexists_tac `{x; y}` >- METIS_TAC [has2clique_i_lem2]);

val ramgraph2rmlem1 = METIS_PROVE [ramseygraph_def,has2clique_i] ``RAMSEYGRAPH 2 r m V E ==> (x:num) IN V ==> y IN V ==> x <> y ==> ~E x y``;

val ramgraph2rmlem2 = TAC_PROOF (
  ``RAMSEYGRAPH 2 r m V E ==> HASANTICLIQUE m V E``,
  rw [hasanticlique_def,hasclique_def] >- qexists_tac `V` >-
  simp [ramseygraph_def] >- METIS_TAC [ramseygraph_e1,ramgraph2rmlem1]);

val ramsey_2_m_m = METIS_PROVE [ramsey_def,ramseygraph_e4,ramgraph2rmlem2] ``RAMSEY 2 m m``;

(* -------------------------------------------------------------------------
   Symmetry of the roles between cliques and anti-cliques
   ------------------------------------------------------------------------- *)

val _ = print_endline "Symmetry";

val sym_compl = TAC_PROOF (``SYM E <=> SYM (\x y.~E x y)``,
  rw [sym_def] >- METIS_TAC []);

val hasclique_compl = TAC_PROOF (
  ``HASCLIQUE r V E <=> HASANTICLIQUE r V (\x y.~E x y)``,
  rw [hasclique_def,hasanticlique_def]);

val hasanticlique_compl = TAC_PROOF (
  ``HASANTICLIQUE r V E <=> HASCLIQUE r V (\x y.~E x y)``,
  rw [hasclique_def,hasanticlique_def]);

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

val combine_count_bijs = TAC_PROOF (
  ``BIJ f (count m) (U:num -> bool) ==> !n V. BIJ g (count n) (V:num -> bool) ==> U INTER V = EMPTY ==> ?h:num -> num. BIJ h (count (m + n)) (U ∪ V) /\ (!i. i < m ==> h i IN U) /\ (!j. m <= j ==> j < m + n ==> h j IN V)``,
  rw [COUNT_SUC] >- qexists_tac `(\ i:num. if i < m then f i else g (i - m))` >-
  BETA_TAC >- CONJ_TAC >- rw [BIJ_DEF] >- rw [INJ_DEF] >- IF_CASES_TAC >-
  METIS_TAC [bij_im_in,COUNT_applied,IN_APP] >- ASM_CASES_TAC ``i - m < n`` >-
  METIS_TAC [bij_im_in,COUNT_applied,IN_APP] >- decide_tac >-
  UNDISCH_TAC ``(if i < m then (f i:num) else g (i - m)) = (if i' < m then f i' else g (i' - m))`` >-
  IF_CASES_TAC >- IF_CASES_TAC >- METIS_TAC [bij_im_inj] >-
  ASM_CASES_TAC ``i' - m < n`` >- DISCH_TAC >-
  ASM_CASES_TAC ``(f (i:num)):num IN U`` >-
  ASM_CASES_TAC ``(g (i' - m)):num IN V`` >-
  ASM_CASES_TAC ``(f (i:num)):num IN U INTER V`` >-
  METIS_TAC [EMPTY_DEF,SPECIFICATION] >-
  UNDISCH_TAC ``~((f (i:num)):num IN U INTER V)`` >- rw [] >-
  METIS_TAC [bij_im_in] >- METIS_TAC [bij_im_in] >- decide_tac >-
  IF_CASES_TAC >- DISCH_TAC >- ASM_CASES_TAC ``i - m < n`` >-
  ASM_CASES_TAC ``(f (i':num)):num IN U`` >-
  ASM_CASES_TAC ``(g (i - m)):num IN V`` >-
  ASM_CASES_TAC ``(f (i':num)):num IN U INTER V`` >-
  METIS_TAC [EMPTY_DEF,SPECIFICATION] >-
  UNDISCH_TAC ``~((f (i':num)):num IN U INTER V)`` >- rw [] >- METIS_TAC [] >-
  METIS_TAC [bij_im_in] >- METIS_TAC [bij_im_in] >- decide_tac >-
  ASM_CASES_TAC ``i - m < n`` >- ASM_CASES_TAC ``i' - m < n`` >- DISCH_TAC >-
  ASM_CASES_TAC ``i - m = i' - m`` >- decide_tac >- METIS_TAC [bij_im_inj] >-
  decide_tac >- decide_tac >- rw [SURJ_DEF] >- IF_CASES_TAC >-
  METIS_TAC [bij_im_in] >- ASM_CASES_TAC ``i - m < n`` >-
  METIS_TAC [bij_im_in] >- decide_tac >- IMP_RES_TAC bij_im_surj >-
  qexists_tac `(x':num)` >- rw [] >- IMP_RES_TAC bij_im_surj >-
  qexists_tac `x' + m` >- rw [] >- CONJ_TAC >- rw [] >-
  METIS_TAC [bij_im_in] >- rw [] >- ASM_CASES_TAC ``j - m < n`` >-
  METIS_TAC [bij_im_in] >- decide_tac);

(* -------------------------------------------------------------------------
   Anti-neighbors
   ------------------------------------------------------------------------- *)

val _ = print_endline "Anti-neighbors";

val lt_0_S = TAC_PROOF (``0 < SUC n``, decide_tac);

val inj_S_ne = METIS_PROVE [lt_0_S,in_count,INJ_DEF] ``INJ f (count (SUC s)) V ==> ?x:num.x IN V``;

val has_size_S_ne = METIS_PROVE [has_size_bij,BIJ_DEF,inj_S_ne] ``V HAS_SIZE SUC n ==> ?x:num.x IN V``;

val hasclique_sub = TAC_PROOF (
  ``HASCLIQUE r U E ==> U SUBSET V ==> HASCLIQUE r V E``,
  rw [hasclique_def] >- METIS_TAC [SUBSET_TRANS]);

val hasanticlique_sub = METIS_PROVE [hasanticlique_def,hasclique_sub] ``HASANTICLIQUE s U E ==> U SUBSET V ==> HASANTICLIQUE s V E``;

val not_self_nbr = METIS_PROVE [nbrs_def,SPECIFICATION] ``~(v IN NBRS V E v)``;

val nbrs_sub = METIS_PROVE [nbrs_def,SPECIFICATION,SUBSET_DEF] ``NBRS V E v SUBSET V``;

val nbrs_finite = METIS_PROVE [nbrs_sub,INFINITE_SUBSET] ``FINITE V ==> FINITE (NBRS V E v)``;

val sub_nbrs_cliq = TAC_PROOF (
  ``SYM E ==> U SUBSET NBRS V E v ==> (!x:num. !y:num. x IN U ==> y IN U ==> x <> y ==> E x y) ==> (!x:num. !y:num. x IN v INSERT U ==> y IN v INSERT U ==> x <> y ==> E x y)``,
  rw [sym_def,SUBSET_DEF,SPECIFICATION,nbrs_def] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC []);

val insert_subset_1 = METIS_PROVE [INSERT_SUBSET] ``(v:num) IN V ==> U SUBSET V ==> v INSERT U SUBSET V``;
val insert_subset_2 = METIS_PROVE [insert_subset_1,nbrs_sub,SUBSET_TRANS] ``(v:num) IN V ==> U SUBSET NBRS V E v ==> v INSERT U SUBSET V``;

val sub_nbrs_hasclique = TAC_PROOF (
  ``SYM E ==> v IN V ==> HASCLIQUE r (NBRS V E v) E ==> HASCLIQUE (SUC r) V E``,
  rw [hasclique_def] >- qexists_tac `v INSERT U` >- CONJ_TAC >-
  METIS_TAC [insert_subset_2] >- CONJ_TAC >-
  METIS_TAC [has_size_insert,not_self_nbr,nbrs_sub,SUBSET_DEF] >-
  METIS_TAC [sub_nbrs_cliq]);

val ramseygraph_nbrs = METIS_PROVE [hasanticlique_sub,nbrs_sub,sub_nbrs_hasclique,ramseygraph_def,hasdeg_def] ``RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> HAS_DEG V E x d ==> RAMSEYGRAPH r s d (NBRS V E x) E``;

val not_self_antinbr = METIS_PROVE [antinbrs_def,SPECIFICATION] ``~(v IN ANTINBRS V E v)``;

val antinbrs_sub = METIS_PROVE [antinbrs_def,SPECIFICATION,SUBSET_DEF] ``ANTINBRS V E v SUBSET V``;

val sub_antinbrs_anticliq = TAC_PROOF (
  ``SYM E ==> U SUBSET ANTINBRS V E v ==> (!x:num. !y:num. x IN U ==> y IN U ==> x <> y ==> ~E x y) ==> (!x:num. !y:num. x IN v INSERT U ==> y IN v INSERT U ==> x <> y ==> ~E x y)``,
  rw [sym_def,SUBSET_DEF,SPECIFICATION,antinbrs_def] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC []);

val insert_subset_3 = METIS_PROVE [insert_subset_1,antinbrs_sub,SUBSET_TRANS] ``(v:num) IN V ==> U SUBSET ANTINBRS V E v ==> v INSERT U SUBSET V``;

val sub_antinbrs_hasanticlique = TAC_PROOF (
  ``SYM E ==> v IN V ==> HASANTICLIQUE r (ANTINBRS V E v) E ==> HASANTICLIQUE (SUC r) V E``,
  rw [hasclique_def,hasanticlique_def] >- qexists_tac `v INSERT U` >-
  CONJ_TAC >- METIS_TAC [insert_subset_3] >- CONJ_TAC >-
  METIS_TAC [has_size_insert,not_self_antinbr,antinbrs_sub,SUBSET_DEF] >-
  METIS_TAC [sub_antinbrs_anticliq]);

val ramseygraph_antinbrs = METIS_PROVE [hasclique_sub,antinbrs_sub,sub_antinbrs_hasanticlique,ramseygraph_def,hasantideg_def] ``RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> RAMSEYGRAPH r s d (ANTINBRS V E x) E``;

val nbrs_antinbrs_union = TAC_PROOF (
  ``NBRS V E v UNION ANTINBRS V E v = V DELETE v``,
  rw [EXTENSION,DELETE_DEF,DIFF_DEF,nbrs_def,antinbrs_def,UNION_DEF,SPECIFICATION] >-
  METIS_TAC []);

val nbrs_antinbrs_inter = TAC_PROOF (
  ``NBRS V E v INTER ANTINBRS V E v = EMPTY``,
  rw [EXTENSION,EMPTY_DEF,nbrs_def,antinbrs_def,INTER_DEF,SPECIFICATION] >-
  METIS_TAC []);

val deg_antideg_sum_lem1 = TAC_PROOF (
  ``V HAS_SIZE SUC n ==> x IN V ==> HAS_DEG V E x d ==> HAS_ANTIDEG V E x d' ==> CARD (NBRS V E x UNION ANTINBRS V E x) + CARD (NBRS V E x INTER ANTINBRS V E x) = n ==> d + d' = n``,
  rw [HAS_SIZE,hasdeg_def,hasantideg_def,CARD_UNION]);

val deg_antideg_sum_lem2 = TAC_PROOF (
  ``V HAS_SIZE SUC n ==> x IN V ==> HAS_DEG V E x d ==> HAS_ANTIDEG V E x d' ==> CARD (NBRS V E x UNION ANTINBRS V E x) + CARD (NBRS V E x INTER ANTINBRS V E x) = n``,
  rw [HAS_SIZE,nbrs_antinbrs_union,nbrs_antinbrs_inter]);

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

val inj_image_sub_has_size = TAC_PROOF (
  ``INJ f (U:num -> bool) (V:num -> bool) ==> U' SUBSET U ==> U' HAS_SIZE m ==> IMAGE f U' HAS_SIZE m``,
  rw [HAS_SIZE] >- ASM_CASES_TAC ``INJ f (U':num -> bool) (V:num -> bool)`` >-
  METIS_TAC [INJ_CARD_IMAGE] >- METIS_TAC [INJ_SUBSET,SUBSET_REFL]);

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

val not_leq_less = TAC_PROOF (``~(m <= n) ==> n < m``, decide_tac);

val ramseygraph_deg_bd = METIS_PROVE [ramseygraph_deg_bd_lem2,not_leq_less] ``RAMSEY r s m ==> RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> HAS_DEG V E x d ==> d < m``;

val ramseygraph_deg_card_bd = METIS_PROVE [ramseygraph_deg_bd,nbrs_card_deg] ``RAMSEY r s m ==> RAMSEYGRAPH (SUC r) s n V E ==> x IN V ==> CARD (NBRS V E x) < m``;

val ramseygraph_antideg_bd_lem1 = METIS_PROVE [ramseygraph_antinbrs,ramsey_def] ``RAMSEY r s d ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> F``;

val ramseygraph_antideg_bd_lem2 = METIS_PROVE [ramseygraph_antideg_bd_lem1,ramsey_mon] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> ~(m <= d)``;

val ramseygraph_antideg_bd = METIS_PROVE [ramseygraph_antideg_bd_lem2,not_leq_less] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> HAS_ANTIDEG V E x d ==> d < m``;

val ramseygraph_antideg_card_bd = METIS_PROVE [ramseygraph_antideg_bd,antinbrs_card_deg] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) n V E ==> x IN V ==> CARD (ANTINBRS V E x) < m``;

val add_lt_l = TAC_PROOF (``k < l ==> m + k < m + l``, decide_tac);

val ramseygraph_deg_card_lower_bd = METIS_PROVE [ramseygraph_antideg_card_bd,deg_antideg_sum_card,add_lt_l] ``RAMSEY r s m ==> RAMSEYGRAPH r (SUC s) (SUC n) V E ==> x IN V ==> n < CARD (NBRS V E x) + m``;

val ramsey_sum_lem1 = TAC_PROOF (
  ``SUC (m + n) < d + SUC m ==> d < SUC n ==> F``,
  decide_tac);

val ramsey_sum_lem2 = METIS_PROVE [ramseygraph_deg_card_lower_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> x IN V ==> SUC (m + n) < CARD (NBRS V E x) + (SUC m)``;

val ramsey_sum_lem3 = METIS_PROVE [ramseygraph_deg_card_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> x IN V ==> CARD (NBRS V E x) < SUC n``;

val ramsey_sum_lem4 = METIS_PROVE [ramsey_sum_lem1,ramsey_sum_lem2,ramsey_sum_lem3] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> x IN V ==> F``;

val ramsey_sum_lem5 = METIS_PROVE [ramsey_sum_lem4,has_size_S_ne,ramseygraph_e1] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (SUC (m + n))) V E ==> F``;

val ramsey_sum = METIS_PROVE [ramsey_sum_lem5,ramsey_def] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEY (SUC r) (SUC s) (SUC (SUC (m + n)))``;

(* -------------------------------------------------------------------------
   R(3,3) <= 6
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,3) <= 6";

val ramsey_0_s_0 = TAC_PROOF (``RAMSEY 0 s 0``,
  rw [ramsey_def,ramseygraph_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``HASCLIQUE 0 V E`` >- METIS_TAC [] >-
  UNDISCH_TAC ``~HASCLIQUE 0 V E`` >- rw [hasclique_def] >-
  qexists_tac `(EMPTY:num -> bool)` >- rw [] >- METIS_TAC [HAS_SIZE_0]);

val bij_count_in = TAC_PROOF (
  ``BIJ f (count m) (U:num -> bool) ==> i < m ==> f i IN U``,
  rw [BIJ_DEF,INJ_DEF]);

val bij_count_neq = TAC_PROOF (
  ``BIJ f (count m) (U:num -> bool) ==> i < m ==> j < m ==> i <> j ==> f i <> f j``,
  rw [BIJ_DEF,INJ_DEF] >- METIS_TAC []);

val ramsey_1_s_1 = TAC_PROOF (``RAMSEY 1 s 1``,
  rw [ramsey_def,ramseygraph_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``HASCLIQUE 1 V E`` >- METIS_TAC [] >-
  UNDISCH_TAC ``~HASCLIQUE 1 V E`` >- rw [hasclique_def] >-
  ASM_CASES_TAC ``(V:num -> bool) HAS_SIZE 1`` >- IMP_RES_TAC has_size_bij >-
  qexists_tac `{f 0}` >- rw [] >- ASM_CASES_TAC ``0 < 1`` >-
  METIS_TAC [bij_count_in] >- decide_tac >- rw [HAS_SIZE] >- METIS_TAC []);

val ramsey_ex = TAC_PROOF (``!r s. ?m. RAMSEY r s (SUC m)``,
  Induct >- GEN_TAC >- qexists_tac `0` >- ASM_CASES_TAC ``SUC 0 = 1`` >-
  ASM_CASES_TAC ``RAMSEY 0 s 1`` >- METIS_TAC [] >-
  ASM_CASES_TAC ``0 <= 1`` >- METIS_TAC [ramsey_0_s_0,ramsey_mon] >-
  decide_tac >- decide_tac >- Induct >- qexists_tac `0` >-
  ASM_CASES_TAC ``SUC 0 = 1`` >- ASM_CASES_TAC ``RAMSEY (SUC r) 0 1`` >-
  METIS_TAC [] >- ASM_CASES_TAC ``0 <= 1`` >-
  METIS_TAC [ramsey_0_s_0,ramsey_mon,ramsey_sym] >- decide_tac >-
  decide_tac >- ASM_CASES_TAC ``?n. RAMSEY r (SUC s) (SUC n)`` >-
  UNDISCH_TAC ``?n. RAMSEY r (SUC s) (SUC n)`` >-
  UNDISCH_TAC ``?m. RAMSEY (SUC r) s (SUC m)`` >- METIS_TAC [ramsey_sum] >-
  METIS_TAC []);

val least_num_thm = TAC_PROOF (
  ``!n:num. (?i:num. i < n /\ p i) ==> ?m:num. p m /\ !k:num. k < m ==> ~p k``,
  Induct >- rw [] >- rw [] >- ASM_CASES_TAC ``?i. i < n /\ p i`` >-
  METIS_TAC [] >- qexists_tac `(i:num)` >- rw [] >- DISCH_TAC >-
  UNDISCH_TAC ``~?i. i < n /\ p i`` >- simp [] >- qexists_tac `(k:num)` >-
  rw []);

val ramsey_ex_least = TAC_PROOF (
  ``!r s. ?m. RAMSEY r s m /\ !n. n < m ==> ~RAMSEY r s n``,
  METIS_TAC [least_num_thm,ramsey_ex]);

val rams_prop = TAC_PROOF (
  ``RAMSEY r s (RAMS r s) /\ !n:num. n < RAMS r s ==> ~RAMSEY r s n``,
  simp [rams_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``?p:num -> bool . ~p (@ m. p m) /\ (?m. p m)`` >-
  METIS_TAC [SELECT_AX] >-
  UNDISCH_TAC ``~?p:num -> bool . ~p (@ m. p m) /\ (?m. p m)`` >- simp [] >-
  qexists_tac `\m:num. RAMSEY r s m /\ !n. n < m ==> ~RAMSEY r s n` >-
  BETA_TAC >- CONJ_TAC >- METIS_TAC [] >- METIS_TAC [ramsey_ex_least]);

val rams_eq_S = TAC_PROOF (
  ``~RAMSEY r s n ==> RAMSEY r s (SUC n) ==> RAMS r s = SUC n``,
  rw [] >- CCONTR_TAC >- ASM_CASES_TAC ``SUC n < RAMS r s`` >-
  METIS_TAC [rams_prop] >- ASM_CASES_TAC ``RAMS r s <= n`` >-
  METIS_TAC [ramsey_mon,rams_prop] >- decide_tac);

val suc_2_3 = TAC_PROOF (``SUC 2 = 3``, decide_tac);

val suc_suc_2_2_6 = TAC_PROOF (``SUC (SUC (2 + 2)) = 6``, decide_tac);

val ramsey_S2_S2_SS22 = METIS_PROVE [ramsey_sum,ramsey_2_m_m,ramsey_m_2_m] ``RAMSEY (SUC 2) (SUC 2) (SUC (SUC (2 + 2)))``;

val ramsey_3_3_6 = METIS_PROVE [ramsey_S2_S2_SS22,suc_2_3,suc_suc_2_2_6] ``RAMSEY 3 3 6``;

(* -------------------------------------------------------------------------
   R(3,4,9) implies all vertices have degree 3
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,4,9) implies all vertices have degree 3";

val ramsey_sum_regular_lem1 = TAC_PROOF (
  ``m + n < d + SUC m ==> d < SUC n ==> d = n``,
  decide_tac);

val ramsey_sum_regular_lem2 = METIS_PROVE [ramseygraph_deg_card_lower_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (m + n)) V E ==> x IN V ==> m + n < CARD (NBRS V E x) + (SUC m)``;

val ramsey_sum_regular_lem3 = METIS_PROVE [ramseygraph_deg_card_bd] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (m + n)) V E ==> x IN V ==> CARD (NBRS V E x) < SUC n``;

val ramsey_sum_regular = METIS_PROVE [ramsey_sum_regular_lem1,ramsey_sum_regular_lem2,ramsey_sum_regular_lem3] ``RAMSEY (SUC r) s (SUC m) ==> RAMSEY r (SUC s) (SUC n) ==> RAMSEYGRAPH (SUC r) (SUC s) (SUC (m + n)) V E ==> x IN V ==> CARD (NBRS V E x) = n``;

val ramseygraph_3_4_9_3regular_lem1 = METIS_PROVE [ramsey_sum_regular] ``RAMSEY (SUC 2) 3 (SUC 5) ==> RAMSEY 2 (SUC 3) (SUC 3) ==> RAMSEYGRAPH (SUC 2) (SUC 3) (SUC (5 + 3)) V E ==> x IN V ==> CARD (NBRS V E x) = 3``;

val suc_3_4 = TAC_PROOF (``SUC 3 = 4``, decide_tac);

val suc_4_5 = TAC_PROOF (``SUC 4 = 5``, decide_tac);

val suc_5_6 = TAC_PROOF (``SUC 5 = 6``, decide_tac);

val suc_5_3_9 = TAC_PROOF (``SUC (5 + 3) = 9``, decide_tac);

val ramseygraph_3_4_9_3regular = METIS_PROVE [ramseygraph_3_4_9_3regular_lem1,suc_2_3,suc_3_4,suc_5_6,suc_5_3_9,ramsey_2_m_m,ramsey_3_3_6] ``RAMSEYGRAPH 3 4 9 V E ==> x IN V ==> CARD (NBRS V E x) = 3``;

(* -------------------------------------------------------------------------
   Infrastructure to prove the sum of degrees must be odd 
   if there is odd number of vertex with odd degrees.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Sum of degrees must be odd";

val eq_3_suc_double_1 = TAC_PROOF (``3 = SUC (2 * 1)``, decide_tac);

val odd_3 = METIS_PROVE [eq_3_suc_double_1,ODD_DOUBLE] ``ODD 3``;

val eq_9_suc_double_4 = TAC_PROOF (``9 = SUC (2 * 4)``, decide_tac);

val odd_9 = METIS_PROVE [eq_9_suc_double_4,ODD_DOUBLE] ``ODD 9``;

val odd_degr_sum_base = METIS_PROVE [CARD_EMPTY,SUM_IMAGE_THM] ``ODD (CARD EMPTY) <=> ODD (SUM_IMAGE (DEGR V E) EMPTY)``;

val odd_degr_sum_ind_lem1 = METIS_PROVE [INSERT_SUBSET,ODD,ODD_ADD] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (SUC (CARD U)) <=> ODD (DEGR V E v + SUM_IMAGE (DEGR V E) U)))``;

val odd_degr_sum_ind_lem2 = METIS_PROVE [odd_degr_sum_ind_lem1,CARD_INSERT] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (CARD (v INSERT U)) <=> ODD (DEGR V E v + SUM_IMAGE (DEGR V E) U)))``;

val odd_degr_sum_ind_lem3 = METIS_PROVE [odd_degr_sum_ind_lem2,DELETE_NON_ELEMENT] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> !U. FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (CARD (v INSERT U)) <=> ODD (DEGR V E v + SUM_IMAGE (DEGR V E) (U DELETE v))))``;

val odd_degr_sum_ind = METIS_PROVE [odd_degr_sum_ind_lem3,SUM_IMAGE_THM] ``(!x. x IN V ==> ODD (DEGR V E x)) ==> !U. FINITE U /\ (U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))) ==> !v. ~(v IN U) ==> (v INSERT U SUBSET V ==> (ODD (CARD (v INSERT U)) <=> ODD (SUM_IMAGE (DEGR V E) (v INSERT U))))``;

val odd_degr_sum = TAC_PROOF (
  ``(!x. x IN V ==> ODD (DEGR V E x)) ==> !U. FINITE U ==> U SUBSET V ==> (ODD (CARD U) <=> ODD (SUM_IMAGE (DEGR V E) U))``,
  DISCH_TAC >- Induct >- CONJ_TAC >- METIS_TAC [odd_degr_sum_base] >-
  METIS_TAC [odd_degr_sum_ind]);

val odd_degr_sum_V = METIS_PROVE [odd_degr_sum,SUBSET_REFL] ``FINITE (V:num -> bool) ==> (!x. x IN V ==> ODD (DEGR V E x)) ==> (ODD (CARD V) <=> ODD (SUM_IMAGE (DEGR V E) V))``;

val ramseygraph_3_4_9_odddegr = METIS_PROVE [ramseygraph_3_4_9_3regular,odd_3,degr_def] ``RAMSEYGRAPH 3 4 9 V E ==> !x.x IN V ==> ODD (DEGR V E x)``;

val ramseygraph_3_4_9_odd_degr_sum = METIS_PROVE [ramseygraph_3_4_9_odddegr,ramseygraph_e1,HAS_SIZE,degr_def,odd_degr_sum_V,odd_9] ``RAMSEYGRAPH 3 4 9 V E ==> ODD (SUM_IMAGE (DEGR V E) V)``;

(* -------------------------------------------------------------------------
   Infrastructure to prove the sum of degrees must be even
   ------------------------------------------------------------------------- *)

val _ = print_endline "Sum of degrees must be even";

val sum_degr_even_lem1 = TAC_PROOF (
  ``SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> !x. x IN V ==> NBRS (e INSERT V) E x = NBRS V E x``,
  rw [nbrs_def,EXTENSION,SPECIFICATION] >- METIS_TAC [sym_def]);

val sum_degr_even_lem2 = TAC_PROOF (
  ``SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> !x. x IN V ==> DEGR (e INSERT V) E x = DEGR V E x``,
  rw [degr_def] >- IMP_RES_TAC sum_degr_even_lem1 >- METIS_TAC []);

val sum_degr_even_lem3 = TAC_PROOF (
  ``SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> NBRS (e INSERT V) E e = EMPTY``,
  rw [nbrs_def,EXTENSION,SPECIFICATION] >- METIS_TAC []);

val sum_degr_even_lem4 = TAC_PROOF (
  ``SYM E ==> ~(e IN V) ==> FINITE V ==> NBRS V E e = EMPTY ==> DEGR (e INSERT V) E e = 0``,
  rw [degr_def] >- IMP_RES_TAC sum_degr_even_lem3 >- METIS_TAC [CARD_EMPTY]);

val sum_degr_even_lem5 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> U SUBSET NBRS V E e``,
  rw [nbrs_def,EXTENSION,SPECIFICATION,SUBSET_DEF]);

val sum_degr_even_lem6 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> ?E'. SYM E' /\ NBRS V E' e = U /\ (!x. x IN V ==> NBRS V E' x = NBRS V E x) /\ e' INSERT NBRS (e INSERT V) E' e = NBRS (e INSERT V) E e /\ (!x. x IN V DELETE e' ==> NBRS (e INSERT V) E' x = NBRS (e INSERT V) E x) /\ NBRS (e INSERT V) E e' = e INSERT NBRS (e INSERT V) E' e' /\ ~(e' IN NBRS (e INSERT V) E' e)``,
  rw [] >- ASM_CASES_TAC ``e' IN NBRS V E e`` >-
  ASM_CASES_TAC ``e' IN (V:num -> bool)`` >-
  qexists_tac `\u v:num. E u v /\ ~(u = e /\ v = e') /\ ~(u = e' /\ v = e)` >-
  CONJ_TAC >- rw [sym_def] >- METIS_TAC [sym_def] >- CONJ_TAC >-
  UNDISCH_TAC ``NBRS V E e = e' INSERT U`` >-
  rw [nbrs_def,EXTENSION,SPECIFICATION] >- EQ_TAC >- METIS_TAC [] >-
  METIS_TAC [sym_def,SPECIFICATION] >- CONJ_TAC >-
  rw [nbrs_def,EXTENSION,SPECIFICATION] >-
  METIS_TAC [sym_def,SPECIFICATION] >- CONJ_TAC >-
  rw [nbrs_def,EXTENSION,SPECIFICATION,INSERT_DEF] >- EQ_TAC >- rw [] >-
  METIS_TAC [nbrs_sub,SUBSET_DEF,SPECIFICATION] >- METIS_TAC [] >-
  METIS_TAC [nbrs_def,SPECIFICATION] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- CONJ_TAC >- GEN_TAC >- DISCH_TAC >-
  rw [nbrs_def,EXTENSION,SPECIFICATION] >- EQ_TAC >- METIS_TAC [] >-
  DISCH_TAC >- CONJ_TAC >- METIS_TAC [] >- CONJ_TAC >- METIS_TAC [] >-
  CONJ_TAC >- METIS_TAC [] >- METIS_TAC [SPECIFICATION] >-
  rw [nbrs_def,EXTENSION,SPECIFICATION] >- EQ_TAC >- METIS_TAC [] >-
  DISCH_TAC >- CONJ_TAC >- METIS_TAC [] >- CONJ_TAC >-
  METIS_TAC [sym_def,nbrs_def,SPECIFICATION] >-
  METIS_TAC [sym_def,nbrs_def,SPECIFICATION] >-
  METIS_TAC [nbrs_def,SPECIFICATION] >- UNDISCH_TAC ``~(e' IN NBRS V E e)`` >-
  rw []);

val sum_degr_even_lem7 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> ?E'. SYM E' /\ NBRS V E' e = U /\ (!x. x IN V ==> NBRS V E' x = NBRS V E x) /\ NBRS (e INSERT V) E e = e' INSERT NBRS (e INSERT V) E' e /\ (!x. x IN V DELETE e' ==> NBRS (e INSERT V) E' x = NBRS (e INSERT V) E x) /\ NBRS (e INSERT V) E e' = e INSERT NBRS (e INSERT V) E' e' /\ ~(e' IN NBRS (e INSERT V) E' e) /\ e' IN NBRS V E e``,
  DISCH_TAC >- DISCH_TAC >- DISCH_TAC >- DISCH_TAC >- DISCH_TAC >-
  IMP_RES_TAC sum_degr_even_lem6 >- qexists_tac `E'` >- CONJ_TAC >-
  METIS_TAC [] >- CONJ_TAC >- METIS_TAC [] >- CONJ_TAC >- METIS_TAC [] >-
  CONJ_TAC >- METIS_TAC [] >- CONJ_TAC >- METIS_TAC [] >- CONJ_TAC >-
  METIS_TAC [] >- CONJ_TAC >- METIS_TAC [] >- simp []);

val sum_degr_even_lem8 = TAC_PROOF (
  ``(!x. x IN V DELETE e' ==> NBRS (e INSERT V) E' x = NBRS (e INSERT V) E x) ==> !x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x``,
  DISCH_TAC >- GEN_TAC >- DISCH_TAC >- rw [degr_def]);

val sum_degr_even_lem9 = TAC_PROOF (
  ``FINITE V ==> NBRS (e INSERT V) E e' = e INSERT NBRS (e INSERT V) E' e' ==> ~(e IN NBRS (e INSERT V) E' e') ==> DEGR (e INSERT V) E e' = SUC (DEGR (e INSERT V) E' e')``,
  DISCH_TAC >- DISCH_TAC >- rw [degr_def] >-
  rw [CARD_INSERT,FINITE_INSERT,nbrs_finite]);


val sum_degr_even_lem10 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> ~(e' IN U) ==> SYM E ==> NBRS V E e = e' INSERT U ==> ?E'. SYM E' /\ NBRS V E' e = U /\ (!x. x IN V ==> DEGR V E' x = DEGR V E x) /\ SUC (DEGR (e INSERT V) E' e) = DEGR (e INSERT V) E e /\ SUC (∑ (DEGR (e INSERT V) E') V) = ∑ (DEGR (e INSERT V) E) V /\ (!x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x)``,
  rw [] >- IMP_RES_TAC sum_degr_even_lem7 >- qexists_tac `E'` >- CONJ_TAC >-
  METIS_TAC [] >- CONJ_TAC >- METIS_TAC [] >- CONJ_TAC >- rw [degr_def] >-
  CONJ_TAC >- rw [degr_def] >-
  ASM_CASES_TAC ``FINITE (NBRS (e INSERT V) E' e)`` >- rw [CARD_INSERT] >-
  METIS_TAC [nbrs_finite,FINITE_INSERT] >-
  ASM_CASES_TAC ``!x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x`` >-
  CONJ_TAC >-
  ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e' INSERT V DELETE e') = SUC (SUM_IMAGE (DEGR (e INSERT V) E') (e' INSERT V DELETE e'))`` >-
  UNDISCH_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e' INSERT V DELETE e') = SUC (SUM_IMAGE (DEGR (e INSERT V) E') (e' INSERT V DELETE e'))`` >-
  ASM_CASES_TAC ``(e':num) IN V`` >- rw [INSERT_DELETE] >-
  METIS_TAC [nbrs_def,SPECIFICATION] >-
  ASM_CASES_TAC ``DEGR (e INSERT V) E e' + SUM_IMAGE (DEGR (e INSERT V) E) (V DELETE e') = SUC (DEGR (e INSERT V) E' e' + ∑ (DEGR (e INSERT V) E') (V DELETE e'))`` >-
  ASM_CASES_TAC ``(e':num) IN V DELETE e'`` >- METIS_TAC [IN_DELETE] >-
  UNDISCH_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e' INSERT V DELETE e') <> SUC (SUM_IMAGE (DEGR (e INSERT V) E') (e' INSERT V DELETE e'))`` >-
  rw [SUM_IMAGE_THM] >-
  ASM_CASES_TAC ``DEGR (e INSERT V) E e' + SUM_IMAGE (DEGR (e INSERT V) E) (V DELETE e') = SUC (DEGR (e INSERT V) E' e') + ∑ (DEGR (e INSERT V) E') (V DELETE e')`` >-
  decide_tac >-
  ASM_CASES_TAC ``DEGR (e INSERT V) E e' = SUC (DEGR (e INSERT V) E' e')`` >-
  ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (V DELETE e') = ∑ (DEGR (e INSERT V) E') (V DELETE e')`` >-
  METIS_TAC [] >- METIS_TAC [SUM_IMAGE_CONG] >-
  ASM_CASES_TAC ``e IN NBRS (e INSERT V) E' e'`` >-
  ASM_CASES_TAC ``e' IN NBRS (e INSERT V) E' e`` >- METIS_TAC [] >-
  ASM_CASES_TAC ``(e':num) IN e INSERT V`` >-
  ASM_CASES_TAC ``(e':num) IN V`` >- METIS_TAC [nbrs_swap] >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- ASM_CASES_TAC ``(e':num) IN V`` >-
  UNDISCH_TAC ``(e':num) IN V`` >-
  UNDISCH_TAC ``~((e':num) IN e INSERT V)`` >- rw [] >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [sum_degr_even_lem9] >-
  UNDISCH_TAC ``!x. x IN V DELETE e' ==> DEGR (e INSERT V) E x = DEGR (e INSERT V) E' x`` >-
  rw [] >- METIS_TAC [sum_degr_even_lem8]);


val sum_degr_even_lem11 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> (!x. x IN C ==> DEGR V E' x = DEGR V E x) ==> SUC (DEGR (e INSERT V) E' e) = DEGR (e INSERT V) E e ==> SUC (SUM_IMAGE (DEGR (e INSERT V) E') V) = ∑ (DEGR (e INSERT V) E) V ==> SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = 2 + SUM_IMAGE (DEGR (e INSERT V) E') (e INSERT V)``,
  rw [SUM_IMAGE_THM,DELETE_NON_ELEMENT]);

val sum_degr_even_lem12 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> !U:num -> bool. FINITE U ==> !E:num -> num -> bool. SYM E ==> NBRS V E e = U ==> SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = SUM_IMAGE (DEGR V E) V + 2 * CARD U``,
  DISCH_TAC >- DISCH_TAC >- Induct >- CONJ_TAC >- GEN_TAC >- DISCH_TAC >-
  DISCH_TAC >- rw [SUM_IMAGE_THM] >-
  ASM_CASES_TAC ``V DELETE e = (V:num -> bool)`` >-
  IMP_RES_TAC sum_degr_even_lem4 >- rw [] >- IMP_RES_TAC sum_degr_even_lem2 >-
  METIS_TAC [SUM_IMAGE_CONG] >- METIS_TAC [DELETE_NON_ELEMENT] >- rw [] >-
  IMP_RES_TAC sum_degr_even_lem10 >- IMP_RES_TAC sum_degr_even_lem11 >-
  ASM_CASES_TAC ``NBRS V E' e = (U:num -> bool)`` >-
  ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E') (e INSERT V) = 2 * CARD (U:num -> bool) + SUM_IMAGE (DEGR V E') V`` >-
  ASM_CASES_TAC ``SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = 2 + SUM_IMAGE (DEGR (e INSERT V) E') (e INSERT V)`` >-
  ASM_CASES_TAC ``SUM_IMAGE (DEGR V E) V = SUM_IMAGE (DEGR V E') V`` >-
  rw [] >- METIS_TAC [SUM_IMAGE_CONG] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC []);

val sum_degr_even_lem13 = TAC_PROOF (
  ``~(e IN V) ==> FINITE V ==> SYM E ==> SUM_IMAGE (DEGR (e INSERT V) E) (e INSERT V) = SUM_IMAGE (DEGR V E) V + 2 * CARD (NBRS V E e)``,
  PROVE_TAC [sum_degr_even_lem12,nbrs_finite]);

val sum_degr_even = TAC_PROOF (
  ``SYM E ==> !V:num -> bool. FINITE V ==> EVEN (SUM_IMAGE (DEGR V E) V)``,
  DISCH_TAC >- Induct >- CONJ_TAC >- rw [SUM_IMAGE_THM] >- rw [] >-
  rw [sum_degr_even_lem13] >- METIS_TAC [EVEN_ADD,EVEN_DOUBLE]);

(* -------------------------------------------------------------------------
   R(3,4) <= 9 (second part)
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,4) <= 9 (second part)";

val ramsey_3_4_9 = TAC_PROOF (``RAMSEY 3 4 9``,
  rw [ramsey_def] >- DISCH_TAC >-
  ASM_CASES_TAC ``ODD (SUM_IMAGE (DEGR V E) V)`` >-
  ASM_CASES_TAC ``EVEN (SUM_IMAGE (DEGR V E) V)`` >-
  METIS_TAC [EVEN_AND_ODD] >-
  METIS_TAC [sum_degr_even,ramseygraph_e1,ramseygraph_e2,HAS_SIZE] >-
  METIS_TAC [ramseygraph_3_4_9_odd_degr_sum]);

val suc_8_9 = TAC_PROOF (``SUC 8 = 9``, decide_tac);

val ramsey_S2_4_S8 = TAC_PROOF (``RAMSEY (SUC 2) 4 (SUC 8)``,
  METIS_TAC [ramsey_3_4_9,suc_2_3,suc_8_9]);

val ramsey_S2_S4_SS84 = TAC_PROOF (
  ``RAMSEY (SUC 2) (SUC 4) (SUC (SUC (8 + 4)))``,
  METIS_TAC [ramsey_sum,ramsey_2_m_m,ramsey_S2_4_S8,suc_3_4]);

(* -------------------------------------------------------------------------
   R(3,5) <= 14
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(3,5) <= 14";

val ramsey_3_5_14 = TAC_PROOF (``RAMSEY 3 5 14``,
  ASM_CASES_TAC ``SUC (SUC (8 + 4)) = 14`` >-
  METIS_TAC [ramsey_S2_S4_SS84,suc_2_3,suc_4_5] >- decide_tac);

(* -------------------------------------------------------------------------
   R(4,4) <= 18
   ------------------------------------------------------------------------- *)

val _ = print_endline "R(4,4) <= 18";

val ramsey_3_S3_S8 = TAC_PROOF (``RAMSEY 3 (SUC 3) (SUC 8)``,
  METIS_TAC [ramsey_3_4_9,suc_3_4,suc_8_9]);

val ramsey_4_4_18 = TAC_PROOF (``RAMSEY 4 4 18``,
  ASM_CASES_TAC ``SUC (SUC (8 + 8)) = 18`` >-
  METIS_TAC [ramsey_sum,ramsey_3_S3_S8,suc_3_4,ramsey_sym] >- decide_tac);

(* -------------------------------------------------------------------------
   Proving that in a R(4,5,25) there exists a vertex of degree 8,10 or 12
   ------------------------------------------------------------------------- *)

val _ = print_endline "Existence of a vertex of degree 8, 10 or 12";

val ramseygraph_4_5_25_upper_bd = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x < 14``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  METIS_TAC [ramseygraph_deg_card_bd,ramsey_3_5_14] >- METIS_TAC [suc_3_4]);

val ramseygraph_4_5_25_lower_bd = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> 6 < DEGR V E x``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) (SUC 24) V E`` >-
  ASM_CASES_TAC ``24 < CARD (NBRS V E x) + 18`` >- decide_tac >-
  METIS_TAC [ramseygraph_deg_card_lower_bd,ramsey_4_4_18] >-
  ASM_CASES_TAC ``SUC 24 = 25`` >- METIS_TAC [suc_4_5] >- decide_tac);

val odd_25 = TAC_PROOF (``ODD 25``,
  ASM_CASES_TAC ``25 = SUC (2 * 12)`` >- METIS_TAC [ODD_DOUBLE] >- decide_tac);

val ramseygraph_4_5_25_ex_even = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ EVEN (DEGR V E x)``,
  rw [] >- CCONTR_TAC >- ASM_CASES_TAC ``!x. x IN V ==> ODD (DEGR V E x)`` >-
  ASM_CASES_TAC ``ODD (SUM_IMAGE (DEGR V E) V)`` >-
  ASM_CASES_TAC ``EVEN (SUM_IMAGE (DEGR V E) V)`` >-
  METIS_TAC [EVEN_AND_ODD] >-
  METIS_TAC [sum_degr_even,ramseygraph_e1,ramseygraph_e2,HAS_SIZE] >-
  METIS_TAC [odd_degr_sum_V,ramseygraph_e1,HAS_SIZE,odd_25] >-
  METIS_TAC [ODD_EVEN]);

val evens_between_6_14_are_8_10_12 = TAC_PROOF (
  ``6 < n ==> n < 14 ==> EVEN n ==> n = 8 \/ n = 10 \/ n = 12``,
  (rw_tac numLib.arith_ss) [] >> pop_assum (Q.X_CHOOSE_THEN `m` SUBST_ALL_TAC o REWRITE_RULE [EVEN_EXISTS, TIMES2]) >> rw_tac numLib.arith_ss []);

val ramseygraph_4_5_25_ex_8_10_12 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ (DEGR V E x = 8 \/ DEGR V E x = 10 \/ DEGR V E x = 12)``,
  rw [] >- IMP_RES_TAC ramseygraph_4_5_25_ex_even >-
  IMP_RES_TAC ramseygraph_4_5_25_lower_bd >-
  IMP_RES_TAC ramseygraph_4_5_25_upper_bd >- qexists_tac `x` >- CONJ_TAC >-
  METIS_TAC [] >- METIS_TAC [evens_between_6_14_are_8_10_12]);

(* -------------------------------------------------------------------------
   Degree 8: connection with the first-order formulation used in
   the computational parts of the proof.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Degree 8";

val add_8_16 = TAC_PROOF (``8 + 16 = 24``, decide_tac);

val add_8_16_alt = TAC_PROOF (``x = 8 ==> y <> 16 ==> x + y = 24 ==> F``,
  decide_tac);

val suc_24_25 = TAC_PROOF (``SUC 24 = 25``, decide_tac);

val r4525_no8_lem1 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> RAMSEYGRAPH 3 5 8 (NBRS V E x) E``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  ASM_CASES_TAC ``HAS_DEG V E x 8`` >- METIS_TAC [ramseygraph_nbrs] >-
  METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite] >-
  METIS_TAC [suc_3_4]);

val r4525_no8_lem2 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> RAMSEYGRAPH 4 4 16 (ANTINBRS V E x) E``,
  rw [] >- IMP_RES_TAC r4525_no8_lem1 >- UNDISCH_TAC ``DEGR V E x = 8`` >-
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E`` >-
  ASM_CASES_TAC ``HAS_ANTIDEG V E x 16`` >-
  METIS_TAC [ramseygraph_antinbrs] >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E`` >-
  IMP_RES_TAC deg_antideg_sum_card >-
  METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_8_16_alt] >-
  METIS_TAC [suc_24_25] >- METIS_TAC [suc_4_5]);

val r4525_no8_lem3 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 8 ==> h i IN NBRS V E x) /\ (!j. 8 <= j ==> j < 24 ==> h j IN ANTINBRS V E x)``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  ASM_CASES_TAC ``HAS_DEG V E x 8`` >- IMP_RES_TAC ramseygraph_nbrs >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E`` >-
  ASM_CASES_TAC ``HAS_ANTIDEG V E x 16`` >-
  IMP_RES_TAC ramseygraph_antinbrs >-
  ASM_CASES_TAC ``(NBRS V E x) HAS_SIZE 8`` >-
  ASM_CASES_TAC ``(ANTINBRS V E x) HAS_SIZE 16`` >-
  IMP_RES_TAC has_size_bij >-
  ASM_CASES_TAC ``NBRS V E x INTER ANTINBRS V E x = EMPTY`` >-
  METIS_TAC [combine_count_bijs,add_8_16] >-
  METIS_TAC [nbrs_antinbrs_inter] >- METIS_TAC [HAS_SIZE,hasantideg_def] >-
  METIS_TAC [HAS_SIZE,hasdeg_def] >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E`` >-
  IMP_RES_TAC deg_antideg_sum_card >-
  METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_8_16_alt] >-
  METIS_TAC [suc_24_25] >- METIS_TAC [suc_4_5] >-
  METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite] >-
  METIS_TAC [suc_3_4]);

val r4525_no8_lem4 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 8 ==> h i IN NBRS V E x) /\ (!j. 8 <= j ==> j < 24 ==> h j IN ANTINBRS V E x) /\ INJ h (count 8) (NBRS V E x) /\ INJ (\i.h (i + 8)) (count 16) (ANTINBRS V E x)``,
  rw [] >- IMP_RES_TAC r4525_no8_lem3 >- qexists_tac `(h:num -> num)` >-
  UNDISCH_TAC ``BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x)`` >-
  rw [BIJ_DEF,INJ_DEF] >- ASM_CASES_TAC ``i + 8 = i' + 8`` >- decide_tac >-
  ASM_CASES_TAC ``i + 8 < 24`` >- ASM_CASES_TAC ``i' + 8 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac);

val r4525_no8_lem5 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> ?E':num -> num -> bool. (!x y. E' x y <=> E' y x) /\ RAMSEYGRAPH 4 5 24 (count 24) E' /\ RAMSEYGRAPH 3 5 8 (count 8) E' /\ RAMSEYGRAPH 4 4 16 (count 16) (\i j.E' (i + 8) (j + 8))``,
  rw [] >- IMP_RES_TAC r4525_no8_lem1 >- IMP_RES_TAC r4525_no8_lem2 >-
  IMP_RES_TAC r4525_no8_lem4 >- qexists_tac `\i j.E (h i) (h j)` >-
  BETA_TAC >- CONJ_TAC >- METIS_TAC [ramseygraph_def,sym_def] >- CONJ_TAC >-
  UNDISCH_TAC ``RAMSEYGRAPH 4 5 25 V E`` >- rw [ramseygraph_def] >-
  METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >- UNDISCH_TAC ``SYM E`` >-
  rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 24`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASCLIQUE 4 V E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 24`` >- ASM_CASES_TAC ``x'' < 8`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x`` >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [] >-
  ASM_CASES_TAC ``8 <= x''`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x`` >-
  METIS_TAC [antinbrs_sub,SUBSET_DEF] >- METIS_TAC [] >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size,BIJ_DEF] >-
  rw [IMAGE_DEF,GSPECIFICATION] >- METIS_TAC [BIJ_DEF,INJ_DEF] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 24`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 V E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 24`` >- ASM_CASES_TAC ``x'' < 8`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x`` >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [] >-
  ASM_CASES_TAC ``8 <= x''`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x`` >-
  METIS_TAC [antinbrs_sub,SUBSET_DEF] >- METIS_TAC [] >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size,BIJ_DEF] >-
  rw [IMAGE_DEF,GSPECIFICATION] >- METIS_TAC [BIJ_DEF,INJ_DEF] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- CONJ_TAC >-
  UNDISCH_TAC ``RAMSEYGRAPH 3 5 8 (NBRS V E x) E`` >- rw [ramseygraph_def] >-
  METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >- UNDISCH_TAC ``SYM E`` >-
  rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 8`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 3`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASCLIQUE 3 (NBRS V E x) E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 8`` >- METIS_TAC [] >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [BIJ_DEF,INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 8`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (NBRS V E x) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 8`` >- METIS_TAC [] >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  UNDISCH_TAC ``RAMSEYGRAPH 4 4 16 (ANTINBRS V E x) E`` >-
  rw [ramseygraph_def] >- METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >-
  UNDISCH_TAC ``SYM E`` >- rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 16`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h (i + 8)):num) (h (j + 8))`` >-
  UNDISCH_TAC ``~HASCLIQUE 4 (ANTINBRS V E x) E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE (\i.h (i + 8)) (U:num -> bool)` >- CONJ_TAC >-
  rw [SUBSET_DEF] >- ASM_CASES_TAC ``i < 16`` >-
  ASM_CASES_TAC ``8 <= i + 8`` >- ASM_CASES_TAC ``i + 8 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [BIJ_DEF,INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 16`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h (i + 8)):num) (h (j + 8))`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 4 (ANTINBRS V E x) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE (\i.h (i + 8)) (U:num -> bool)` >- CONJ_TAC >-
  rw [SUBSET_DEF] >- ASM_CASES_TAC ``i < 16`` >-
  ASM_CASES_TAC ``8 <= i + 8`` >- ASM_CASES_TAC ``i + 8 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC []);

val r4416_c4416_thm = TAC_PROOF (
  ``RAMSEYGRAPH 4 4 16 (count 16) E ==> C4416b E /\ C4416r E``,
  rw [ramseygraph_def,sym_def,c4416b_def,c4416r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 4 (count 16) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 4 (count 16) E`` >-
  rw [hasanticlique_def,hasclique_def] >- qexists_tac `{x0; x1; x2; x3}` >-
  CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >- rw [HAS_SIZE] >- rw [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC []);

val r358_c358_thm = TAC_PROOF (
  ``RAMSEYGRAPH 3 5 8 (count 8) E ==> C358b E /\ C358r E``,
  rw [ramseygraph_def,sym_def,c358b_def,c358r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 3 (count 8) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (count 8) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3; x4}` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  CONJ_TAC >- rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC []);

val r4524_c4524_thm = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 24 (count 24) E ==> C4524b E /\ C4524r E``,
  rw [ramseygraph_def,sym_def,c4524b_def,c4524r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 4 (count 24) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (count 24) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3; x4}` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  CONJ_TAC >- rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC []);

val hasclique_4_e = TAC_PROOF (
  ``HASCLIQUE 4 V E ==> ?x0 x1 x2 x3:num. x0 IN V /\ x1 IN V /\ x2 IN V /\ x3 IN V /\ x0 <> x1 /\ x0 <> x2 /\ x0 <> x3 /\ x1 <> x2 /\ x1 <> x3 /\ x2 <> x3 /\ E x0 x1 /\ E x0 x2 /\ E x0 x3 /\ E x1 x2 /\ E x1 x3 /\ E x2 x3``,
  rw [hasclique_def] >- IMP_RES_TAC has_size_bij >- qexists_tac `f 0` >-
  qexists_tac `f 1` >- qexists_tac `f 2` >- qexists_tac `f 3` >-
  ASM_CASES_TAC ``0 < 4`` >- ASM_CASES_TAC ``1 < 4`` >-
  ASM_CASES_TAC ``2 < 4`` >- ASM_CASES_TAC ``3 < 4`` >-
  IMP_RES_TAC bij_count_in >- ASM_CASES_TAC ``0 = 1`` >- CCONTR_TAC >-
  UNDISCH_TAC ``0 = 1`` >- decide_tac >- ASM_CASES_TAC ``0 = 2`` >-
  CCONTR_TAC >- UNDISCH_TAC ``0 = 2`` >- decide_tac >-
  ASM_CASES_TAC ``0 = 3`` >- CCONTR_TAC >- UNDISCH_TAC ``0 = 3`` >-
  decide_tac >- ASM_CASES_TAC ``1 = 2`` >- CCONTR_TAC >-
  UNDISCH_TAC ``1 = 2`` >- decide_tac >- ASM_CASES_TAC ``1 = 3`` >-
  CCONTR_TAC >- UNDISCH_TAC ``1 = 3`` >- decide_tac >-
  ASM_CASES_TAC ``2 = 3`` >- CCONTR_TAC >- UNDISCH_TAC ``2 = 3`` >-
  decide_tac >- IMP_RES_TAC bij_count_neq >- METIS_TAC [SUBSET_DEF] >-
  CCONTR_TAC >- UNDISCH_TAC ``~(3 < 4)`` >- decide_tac >- CCONTR_TAC >-
  UNDISCH_TAC ``~(2 < 4)`` >- decide_tac >- CCONTR_TAC >-
  UNDISCH_TAC ``~(1 < 4)`` >- decide_tac >- CCONTR_TAC >-
  UNDISCH_TAC ``~(0 < 4)`` >- decide_tac);

val hasanticlique_5_e = TAC_PROOF (
  ``HASANTICLIQUE 5 V E ==> ?x0 x1 x2 x3 x4:num. x0 IN V /\ x1 IN V /\ x2 IN V /\ x3 IN V /\ x4 IN V /\ x0 <> x1 /\ x0 <> x2 /\ x0 <> x3 /\ x0 <> x4 /\ x1 <> x2 /\ x1 <> x3 /\ x1 <> x4 /\ x2 <> x3 /\ x2 <> x4 /\ x3 <> x4 /\ ~E x0 x1 /\ ~E x0 x2 /\ ~E x0 x3 /\ ~E x0 x4 /\ ~E x1 x2 /\ ~E x1 x3 /\ ~E x1 x4 /\ ~E x2 x3 /\ ~E x2 x4 /\ ~E x3 x4``,
  rw [hasanticlique_def,hasclique_def] >- IMP_RES_TAC has_size_bij >-
  qexists_tac `f 0` >- qexists_tac `f 1` >- qexists_tac `f 2` >-
  qexists_tac `f 3` >- qexists_tac `f 4` >- ASM_CASES_TAC ``0 < 5`` >-
  ASM_CASES_TAC ``1 < 5`` >- ASM_CASES_TAC ``2 < 5`` >-
  ASM_CASES_TAC ``3 < 5`` >- ASM_CASES_TAC ``4 < 5`` >-
  IMP_RES_TAC bij_count_in >- ASM_CASES_TAC ``0 = 1`` >- CCONTR_TAC >-
  UNDISCH_TAC ``0 = 1`` >- decide_tac >- ASM_CASES_TAC ``0 = 2`` >-
  CCONTR_TAC >- UNDISCH_TAC ``0 = 2`` >- decide_tac >-
  ASM_CASES_TAC ``0 = 3`` >- CCONTR_TAC >- UNDISCH_TAC ``0 = 3`` >-
  decide_tac >- ASM_CASES_TAC ``0 = 4`` >- CCONTR_TAC >-
  UNDISCH_TAC ``0 = 4`` >- decide_tac >- ASM_CASES_TAC ``1 = 2`` >-
  CCONTR_TAC >- UNDISCH_TAC ``1 = 2`` >- decide_tac >-
  ASM_CASES_TAC ``1 = 3`` >- CCONTR_TAC >- UNDISCH_TAC ``1 = 3`` >-
  decide_tac >- ASM_CASES_TAC ``1 = 4`` >- CCONTR_TAC >-
  UNDISCH_TAC ``1 = 4`` >- decide_tac >- ASM_CASES_TAC ``2 = 3`` >-
  CCONTR_TAC >- UNDISCH_TAC ``2 = 3`` >- decide_tac >-
  ASM_CASES_TAC ``2 = 4`` >- CCONTR_TAC >- UNDISCH_TAC ``2 = 4`` >-
  decide_tac >- ASM_CASES_TAC ``3 = 4`` >- CCONTR_TAC >-
  UNDISCH_TAC ``3 = 4`` >- decide_tac >- IMP_RES_TAC bij_count_neq >-
  METIS_TAC [SUBSET_DEF] >- CCONTR_TAC >- UNDISCH_TAC ``~(4 < 5)`` >-
  decide_tac >- CCONTR_TAC >- UNDISCH_TAC ``~(3 < 5)`` >- decide_tac >-
  CCONTR_TAC >- UNDISCH_TAC ``~(2 < 5)`` >- decide_tac >- CCONTR_TAC >-
  UNDISCH_TAC ``~(1 < 5)`` >- decide_tac >- CCONTR_TAC >-
  UNDISCH_TAC ``~(0 < 5)`` >- decide_tac);

val c4524_r4524_thm = TAC_PROOF (
  ``SYM E ==> C4524b E /\ C4524r E ==> RAMSEYGRAPH 4 5 24 (count 24) E``,
  rw [ramseygraph_def,sym_def,c4524b_def,c4524r_def] >-
  METIS_TAC [HAS_SIZE,FINITE_COUNT,CARD_COUNT] >- DISCH_TAC >-
  IMP_RES_TAC hasclique_4_e >- ASM_CASES_TAC ``x0 < 24`` >-
  ASM_CASES_TAC ``x1 < 24`` >- ASM_CASES_TAC ``x2 < 24`` >-
  ASM_CASES_TAC ``x3 < 24`` >- PROVE_TAC [] >-
  UNDISCH_TAC ``x3 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x2 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x1 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x0 IN count 24`` >- simp [] >- DISCH_TAC >-
  IMP_RES_TAC hasanticlique_5_e >- ASM_CASES_TAC ``x0 < 24`` >-
  ASM_CASES_TAC ``x1 < 24`` >- ASM_CASES_TAC ``x2 < 24`` >-
  ASM_CASES_TAC ``x3 < 24`` >- ASM_CASES_TAC ``x4 < 24`` >- PROVE_TAC [] >-
  UNDISCH_TAC ``x4 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x3 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x2 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x1 IN count 24`` >- simp [] >-
  UNDISCH_TAC ``x0 IN count 24`` >- simp []);

val r4525_no_deg8 = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 8 ==> F``,
  rw [] >- DISCH_TAC >- IMP_RES_TAC r4525_no8_lem5 >-
  IMP_RES_TAC r358_c358_thm >- IMP_RES_TAC r4416_c4416_thm >-
  IMP_RES_TAC r4524_c4524_thm >- METIS_TAC []);

(* -------------------------------------------------------------------------
   Degree 10: connection with the first-order formulation used in
   the computational parts of the proof.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Degree 10";

val add_10_14 = TAC_PROOF (``10 + 14 = 24``, decide_tac);

val add_10_14_alt = TAC_PROOF (``x = 10 ==> y <> 14 ==> x + y = 24 ==> F``,
  decide_tac);

val r4525_no10_lem1 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> RAMSEYGRAPH 3 5 10 (NBRS V E x) E``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  ASM_CASES_TAC ``HAS_DEG V E x 10`` >- METIS_TAC [ramseygraph_nbrs] >-
  METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite] >-
  METIS_TAC [suc_3_4]);

val r4525_no10_lem2 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> RAMSEYGRAPH 4 4 14 (ANTINBRS V E x) E``,
  rw [] >- IMP_RES_TAC r4525_no10_lem1 >- UNDISCH_TAC ``DEGR V E x = 10`` >-
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E`` >-
  ASM_CASES_TAC ``HAS_ANTIDEG V E x 14`` >-
  METIS_TAC [ramseygraph_antinbrs] >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E`` >-
  IMP_RES_TAC deg_antideg_sum_card >-
  METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_10_14_alt] >-
  METIS_TAC [suc_24_25] >- METIS_TAC [suc_4_5]);

val r4525_no10_lem3 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 10 ==> h i IN NBRS V E x) /\ (!j. 10 <= j ==> j < 24 ==> h j IN ANTINBRS V E x)``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  ASM_CASES_TAC ``HAS_DEG V E x 10`` >- IMP_RES_TAC ramseygraph_nbrs >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E`` >-
  ASM_CASES_TAC ``HAS_ANTIDEG V E x 14`` >-
  IMP_RES_TAC ramseygraph_antinbrs >-
  ASM_CASES_TAC ``(NBRS V E x) HAS_SIZE 10`` >-
  ASM_CASES_TAC ``(ANTINBRS V E x) HAS_SIZE 14`` >-
  IMP_RES_TAC has_size_bij >-
  ASM_CASES_TAC ``NBRS V E x INTER ANTINBRS V E x = EMPTY`` >-
  METIS_TAC [combine_count_bijs,add_10_14] >-
  METIS_TAC [nbrs_antinbrs_inter] >- METIS_TAC [HAS_SIZE,hasantideg_def] >-
  METIS_TAC [HAS_SIZE,hasdeg_def] >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E`` >-
  IMP_RES_TAC deg_antideg_sum_card >-
  METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_10_14_alt] >-
  METIS_TAC [suc_24_25] >- METIS_TAC [suc_4_5] >-
  METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite] >-
  METIS_TAC [suc_3_4]);

val r4525_no10_lem4 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 10 ==> h i IN NBRS V E x) /\ (!j. 10 <= j ==> j < 24 ==> h j IN ANTINBRS V E x) /\ INJ h (count 10) (NBRS V E x) /\ INJ (\i.h (i + 10)) (count 14) (ANTINBRS V E x)``,
  rw [] >- IMP_RES_TAC r4525_no10_lem3 >- qexists_tac `(h:num -> num)` >-
  UNDISCH_TAC ``BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x)`` >-
  rw [BIJ_DEF,INJ_DEF] >- ASM_CASES_TAC ``i + 10 = i' + 10`` >- decide_tac >-
  ASM_CASES_TAC ``i + 10 < 24`` >- ASM_CASES_TAC ``i' + 10 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac);

val r4525_no10_lem5 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> ?E':num -> num -> bool. (!x y. E' x y <=> E' y x) /\ RAMSEYGRAPH 4 5 24 (count 24) E' /\ RAMSEYGRAPH 3 5 10 (count 10) E' /\ RAMSEYGRAPH 4 4 14 (count 14) (\i j.E' (i + 10) (j + 10))``,
  rw [] >- IMP_RES_TAC r4525_no10_lem1 >- IMP_RES_TAC r4525_no10_lem2 >-
  IMP_RES_TAC r4525_no10_lem4 >- qexists_tac `\i j.E (h i) (h j)` >-
  BETA_TAC >- CONJ_TAC >- METIS_TAC [ramseygraph_def,sym_def] >- CONJ_TAC >-
  UNDISCH_TAC ``RAMSEYGRAPH 4 5 25 V E`` >- rw [ramseygraph_def] >-
  METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >- UNDISCH_TAC ``SYM E`` >-
  rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 24`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASCLIQUE 4 V E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 24`` >- ASM_CASES_TAC ``x'' < 10`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x`` >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [] >-
  ASM_CASES_TAC ``10 <= x''`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x`` >-
  METIS_TAC [antinbrs_sub,SUBSET_DEF] >- METIS_TAC [] >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size,BIJ_DEF] >-
  rw [IMAGE_DEF,GSPECIFICATION] >- METIS_TAC [BIJ_DEF,INJ_DEF] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 24`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 V E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 24`` >- ASM_CASES_TAC ``x'' < 10`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x`` >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [] >-
  ASM_CASES_TAC ``10 <= x''`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x`` >-
  METIS_TAC [antinbrs_sub,SUBSET_DEF] >- METIS_TAC [] >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size,BIJ_DEF] >-
  rw [IMAGE_DEF,GSPECIFICATION] >- METIS_TAC [BIJ_DEF,INJ_DEF] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- CONJ_TAC >-
  UNDISCH_TAC ``RAMSEYGRAPH 3 5 10 (NBRS V E x) E`` >- rw [ramseygraph_def] >-
  METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >- UNDISCH_TAC ``SYM E`` >-
  rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 10`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 3`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASCLIQUE 3 (NBRS V E x) E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 10`` >- METIS_TAC [] >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [BIJ_DEF,INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 10`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (NBRS V E x) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 10`` >- METIS_TAC [] >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  UNDISCH_TAC ``RAMSEYGRAPH 4 4 14 (ANTINBRS V E x) E`` >-
  rw [ramseygraph_def] >- METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >-
  UNDISCH_TAC ``SYM E`` >- rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 14`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h (i + 10)):num) (h (j + 10))`` >-
  UNDISCH_TAC ``~HASCLIQUE 4 (ANTINBRS V E x) E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE (\i.h (i + 10)) (U:num -> bool)` >- CONJ_TAC >-
  rw [SUBSET_DEF] >- ASM_CASES_TAC ``i < 14`` >-
  ASM_CASES_TAC ``10 <= i + 10`` >- ASM_CASES_TAC ``i + 10 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [BIJ_DEF,INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 14`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h (i + 10)):num) (h (j + 10))`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 4 (ANTINBRS V E x) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE (\i.h (i + 10)) (U:num -> bool)` >- CONJ_TAC >-
  rw [SUBSET_DEF] >- ASM_CASES_TAC ``i < 14`` >-
  ASM_CASES_TAC ``10 <= i + 10`` >- ASM_CASES_TAC ``i + 10 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC []);



val r4414_c4414_thm = TAC_PROOF (
  ``RAMSEYGRAPH 4 4 14 (count 14) E ==> C4414b E /\ C4414r E``,
  rw [ramseygraph_def,sym_def,c4414b_def,c4414r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 4 (count 14) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 4 (count 14) E`` >-
  rw [hasanticlique_def,hasclique_def] >- qexists_tac `{x0; x1; x2; x3}` >-
  CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >- rw [HAS_SIZE] >- rw [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC []);

val r3510_c3510_thm = TAC_PROOF (
  ``RAMSEYGRAPH 3 5 10 (count 10) E ==> C3510b E /\ C3510r E``,
  rw [ramseygraph_def,sym_def,c3510b_def,c3510r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 3 (count 10) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (count 10) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3; x4}` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  CONJ_TAC >- rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC []);

val r4525_no_deg10 = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 10 ==> F``,
  rw [] >- DISCH_TAC >- IMP_RES_TAC r4525_no10_lem5 >-
  IMP_RES_TAC r3510_c3510_thm >- IMP_RES_TAC r4414_c4414_thm >-
  IMP_RES_TAC r4524_c4524_thm >- METIS_TAC []);

(* -------------------------------------------------------------------------
   Degree 12: connection with the first-order formulation used in
   the computational parts of the proof.
   ------------------------------------------------------------------------- *)

val _ = print_endline "Degree 12";

val add_12_12 = TAC_PROOF (``12 + 12 = 24``, decide_tac);

val add_12_12_alt = TAC_PROOF (``x = 12 ==> y <> 12 ==> x + y = 24 ==> F``,
  decide_tac);

val r4525_no12_lem1 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> RAMSEYGRAPH 3 5 12 (NBRS V E x) E``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  ASM_CASES_TAC ``HAS_DEG V E x 12`` >- METIS_TAC [ramseygraph_nbrs] >-
  METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite] >-
  METIS_TAC [suc_3_4]);

val r4525_no12_lem2 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> RAMSEYGRAPH 4 4 12 (ANTINBRS V E x) E``,
  rw [] >- IMP_RES_TAC r4525_no12_lem1 >- UNDISCH_TAC ``DEGR V E x = 12`` >-
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E`` >-
  ASM_CASES_TAC ``HAS_ANTIDEG V E x 12`` >-
  METIS_TAC [ramseygraph_antinbrs] >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E`` >-
  IMP_RES_TAC deg_antideg_sum_card >-
  METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_12_12_alt] >-
  METIS_TAC [suc_24_25] >- METIS_TAC [suc_4_5]);

val r4525_no12_lem3 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 12 ==> h i IN NBRS V E x) /\ (!j. 12 <= j ==> j < 24 ==> h j IN ANTINBRS V E x)``,
  rw [degr_def] >- ASM_CASES_TAC ``RAMSEYGRAPH (SUC 3) 5 25 V E`` >-
  ASM_CASES_TAC ``HAS_DEG V E x 12`` >- IMP_RES_TAC ramseygraph_nbrs >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 (SUC 4) 25 V E`` >-
  ASM_CASES_TAC ``HAS_ANTIDEG V E x 12`` >-
  IMP_RES_TAC ramseygraph_antinbrs >-
  ASM_CASES_TAC ``(NBRS V E x) HAS_SIZE 12`` >-
  ASM_CASES_TAC ``(ANTINBRS V E x) HAS_SIZE 12`` >-
  IMP_RES_TAC has_size_bij >-
  ASM_CASES_TAC ``NBRS V E x INTER ANTINBRS V E x = EMPTY`` >-
  METIS_TAC [combine_count_bijs,add_12_12] >-
  METIS_TAC [nbrs_antinbrs_inter] >- METIS_TAC [HAS_SIZE,hasantideg_def] >-
  METIS_TAC [HAS_SIZE,hasdeg_def] >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 (SUC 24) V E`` >-
  IMP_RES_TAC deg_antideg_sum_card >-
  METIS_TAC [hasantideg_def,HAS_SIZE,ramseygraph_antinbrs_finite,hasdeg_def,add_12_12_alt] >-
  METIS_TAC [suc_24_25] >- METIS_TAC [suc_4_5] >-
  METIS_TAC [hasdeg_def,HAS_SIZE,ramseygraph_nbrs_finite] >-
  METIS_TAC [suc_3_4]);

val r4525_no12_lem4 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> ?h:num -> num. BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x) /\ (!i. i < 12 ==> h i IN NBRS V E x) /\ (!j. 12 <= j ==> j < 24 ==> h j IN ANTINBRS V E x) /\ INJ h (count 12) (NBRS V E x) /\ INJ (\i.h (i + 12)) (count 12) (ANTINBRS V E x)``,
  rw [] >- IMP_RES_TAC r4525_no12_lem3 >- qexists_tac `(h:num -> num)` >-
  UNDISCH_TAC ``BIJ h (count 24) (NBRS V E x ∪ ANTINBRS V E x)`` >-
  rw [BIJ_DEF,INJ_DEF] >- ASM_CASES_TAC ``i + 12 = i' + 12`` >- decide_tac >-
  ASM_CASES_TAC ``i + 12 < 24`` >- ASM_CASES_TAC ``i' + 12 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac);

val r4525_no12_lem5 = TAC_PROOF (
  ``RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> ?E':num -> num -> bool. (!x y. E' x y <=> E' y x) /\ RAMSEYGRAPH 4 5 24 (count 24) E' /\ RAMSEYGRAPH 3 5 12 (count 12) E' /\ RAMSEYGRAPH 4 4 12 (count 12) (\i j.E' (i + 12) (j + 12))``,
  rw [] >- IMP_RES_TAC r4525_no12_lem1 >- IMP_RES_TAC r4525_no12_lem2 >-
  IMP_RES_TAC r4525_no12_lem4 >- qexists_tac `\i j.E (h i) (h j)` >-
  BETA_TAC >- CONJ_TAC >- METIS_TAC [ramseygraph_def,sym_def] >- CONJ_TAC >-
  UNDISCH_TAC ``RAMSEYGRAPH 4 5 25 V E`` >- rw [ramseygraph_def] >-
  METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >- UNDISCH_TAC ``SYM E`` >-
  rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 24`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASCLIQUE 4 V E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 24`` >- ASM_CASES_TAC ``x'' < 12`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x`` >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [] >-
  ASM_CASES_TAC ``12 <= x''`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x`` >-
  METIS_TAC [antinbrs_sub,SUBSET_DEF] >- METIS_TAC [] >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size,BIJ_DEF] >-
  rw [IMAGE_DEF,GSPECIFICATION] >- METIS_TAC [BIJ_DEF,INJ_DEF] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 24`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 V E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 24`` >- ASM_CASES_TAC ``x'' < 12`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN NBRS V E x`` >-
  METIS_TAC [nbrs_sub,SUBSET_DEF] >- METIS_TAC [] >-
  ASM_CASES_TAC ``12 <= x''`` >-
  ASM_CASES_TAC ``(h:num -> num) x'' IN ANTINBRS V E x`` >-
  METIS_TAC [antinbrs_sub,SUBSET_DEF] >- METIS_TAC [] >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size,BIJ_DEF] >-
  rw [IMAGE_DEF,GSPECIFICATION] >- METIS_TAC [BIJ_DEF,INJ_DEF] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- CONJ_TAC >-
  UNDISCH_TAC ``RAMSEYGRAPH 3 5 12 (NBRS V E x) E`` >- rw [ramseygraph_def] >-
  METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >- UNDISCH_TAC ``SYM E`` >-
  rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 12`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 3`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASCLIQUE 3 (NBRS V E x) E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 12`` >- METIS_TAC [] >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [BIJ_DEF,INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 12`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 5`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h i):num) (h j)`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (NBRS V E x) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE h (U:num -> bool)` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  ASM_CASES_TAC ``x'' < 12`` >- METIS_TAC [] >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  UNDISCH_TAC ``RAMSEYGRAPH 4 4 12 (ANTINBRS V E x) E`` >-
  rw [ramseygraph_def] >- METIS_TAC [CARD_COUNT,FINITE_COUNT,HAS_SIZE] >-
  UNDISCH_TAC ``SYM E`` >- rw [sym_def] >- rw [hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 12`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> E ((h (i + 12)):num) (h (j + 12))`` >-
  UNDISCH_TAC ``~HASCLIQUE 4 (ANTINBRS V E x) E`` >- rw [hasclique_def] >-
  qexists_tac `IMAGE (\i.h (i + 12)) (U:num -> bool)` >- CONJ_TAC >-
  rw [SUBSET_DEF] >- ASM_CASES_TAC ``i < 12`` >-
  ASM_CASES_TAC ``12 <= i + 12`` >- ASM_CASES_TAC ``i + 12 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [BIJ_DEF,INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- rw [hasanticlique_def,hasclique_def] >- CCONTR_TAC >-
  ASM_CASES_TAC ``U SUBSET count 12`` >-
  ASM_CASES_TAC ``(U:num -> bool) HAS_SIZE 4`` >-
  ASM_CASES_TAC ``!i j. i IN (U:num -> bool) ==> j IN U ==> i <> j ==> ~E ((h (i + 12)):num) (h (j + 12))`` >-
  UNDISCH_TAC ``~HASANTICLIQUE 4 (ANTINBRS V E x) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `IMAGE (\i.h (i + 12)) (U:num -> bool)` >- CONJ_TAC >-
  rw [SUBSET_DEF] >- ASM_CASES_TAC ``i < 12`` >-
  ASM_CASES_TAC ``12 <= i + 12`` >- ASM_CASES_TAC ``i + 12 < 24`` >-
  METIS_TAC [] >- decide_tac >- decide_tac >-
  METIS_TAC [SUBSET_DEF,IN_COUNT] >- CONJ_TAC >-
  METIS_TAC [inj_image_sub_has_size] >- rw [IMAGE_DEF,GSPECIFICATION] >-
  METIS_TAC [INJ_DEF] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC []);

(* -------------------------------------------------------------------------
   Connecting with the representations use in the other part of the proof.
   ------------------------------------------------------------------------- *)

val r4412_c4412_thm = TAC_PROOF (
  ``RAMSEYGRAPH 4 4 12 (count 12) E ==> C4412b E /\ C4412r E``,
  rw [ramseygraph_def,sym_def,c4412b_def,c4412r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 4 (count 12) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 4 (count 12) E`` >-
  rw [hasanticlique_def,hasclique_def] >- qexists_tac `{x0; x1; x2; x3}` >-
  CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >- rw [HAS_SIZE] >- rw [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC []);

val r3512_c3512_thm = TAC_PROOF (
  ``RAMSEYGRAPH 3 5 12 (count 12) E ==> C3512b E /\ C3512r E``,
  rw [ramseygraph_def,sym_def,c3512b_def,c3512r_def] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASCLIQUE 3 (count 12) E`` >- rw [hasclique_def] >-
  qexists_tac `{x0; x1; x2}` >- CONJ_TAC >- rw [SUBSET_DEF] >- CONJ_TAC >-
  rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~HASANTICLIQUE 5 (count 12) E`` >-
  rw [hasanticlique_def,hasclique_def] >-
  qexists_tac `{x0; x1; x2; x3; x4}` >- CONJ_TAC >- rw [SUBSET_DEF] >-
  CONJ_TAC >- rw [HAS_SIZE] >- rw [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >- METIS_TAC [] >-
  METIS_TAC [] >- METIS_TAC []);

val r4525_no_deg12 = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> !x. x IN V ==> DEGR V E x = 12 ==> F``,
  rw [] >- DISCH_TAC >- IMP_RES_TAC r4525_no12_lem5 >-
  IMP_RES_TAC r3512_c3512_thm >- IMP_RES_TAC r4412_c4412_thm >-
  IMP_RES_TAC r4524_c4524_thm >- METIS_TAC []);

(* -------------------------------------------------------------------------
   Final theorem, if there is no vertex of degree 8,10 or 12
   and R(4,5) > 24, then we have R(4,5) = 25
   ------------------------------------------------------------------------- *)

val ramseygraph_4_5_25_ex_10_12_hyp = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ (DEGR V E x = 10 \/ DEGR V E x = 12)``,
  METIS_TAC [ramseygraph_4_5_25_ex_8_10_12,r4525_no_deg8]);

val ramseygraph_4_5_25_ex_12_hyp = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEYGRAPH 4 5 25 V E ==> ?x. x IN V /\ DEGR V E x = 12``,
  METIS_TAC [ramseygraph_4_5_25_ex_10_12_hyp,r4525_no_deg10]);

val no_ramseygraph_4_5_25_hyp = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> ~RAMSEYGRAPH 4 5 25 V E``,
  DISCH_TAC >- IMP_RES_TAC ramseygraph_4_5_25_ex_12_hyp >-
  METIS_TAC [r4525_no_deg12]);

val ramsey_4_5_25_hyp1 = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> RAMSEY 4 5 25``,
  rw [ramsey_def] >- METIS_TAC [no_ramseygraph_4_5_25_hyp]);


val ramsey_4_5_25_hyp_top = TAC_PROOF (
  ``(!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C358b E ==> C358r E ==> C4416b (\x y. E (x + 8) (y + 8)) ==> C4416r (\x y. E (x + 8) (y + 8)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3510b E ==> C3510r E ==> C4414b (\x y. E (x + 10) (y + 10)) ==> C4414r (\x y. E (x + 10) (y + 10)) ==> C4524b E ==> C4524r E ==> F) ==> (!E:num -> num -> bool. (!(x:num) (y:num). E x y <=> E y x) ==> C3512b E ==> C3512r E ==> C4412b (\x y. E (x + 12) (y + 12)) ==> C4412r (\x y. E (x + 12) (y + 12)) ==> C4524b E ==> C4524r E ==> F) ==> (?E:num -> num -> bool . SYM E /\ C4524b E /\ C4524r E) ==> RAMS 4 5 = 25``,
  DISCH_TAC >- DISCH_TAC >- DISCH_TAC >- IMP_RES_TAC ramsey_4_5_25_hyp1 >-
  rw [] >- ASM_CASES_TAC ``RAMSEY 4 5 24`` >-
  ASM_CASES_TAC ``RAMSEYGRAPH 4 5 24 (count 24) E`` >- CCONTR_TAC >-
  UNDISCH_TAC ``RAMSEY 4 5 24`` >- rw [ramsey_def] >-
  qexists_tac `(count 24)` >- qexists_tac `E:num->num->bool` >-
  METIS_TAC [] >- CCONTR_TAC >-
  UNDISCH_TAC ``~RAMSEYGRAPH 4 5 24 (count 24) E`` >- simp [] >-
  METIS_TAC [c4524_r4524_thm] >- ASM_CASES_TAC ``RAMSEY 4 5 (SUC 24)`` >-
  IMP_RES_TAC rams_eq_S >- decide_tac >- CCONTR_TAC >-
  UNDISCH_TAC ``~RAMSEY 4 5 (SUC 24)`` >- simp []);

val ramsey_4_5_25_hyp = 
  save_thm ("ramsey_4_5_25_hyp", UNDISCH_ALL ramsey_4_5_25_hyp_top);

val _ = export_theory ();

