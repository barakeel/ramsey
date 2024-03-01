(* =========================================================================
   Proves the existence of a graph satisfying r4524
   ========================================================================= *)

load "syntax"; open aiLib kernel syntax;
load "graph"; open graph;

val ERR = mk_HOL_ERR "test";
val bluethm = ASSUME (noclique 24 (4,true));
val redthm = ASSUME (noclique 24 (5,false));

(* -------------------------------------------------------------------------
   Syntax
   ------------------------------------------------------------------------- *)

fun Eij (i,j) = list_mk_comb (E,[numSyntax.term_of_int i,numSyntax.term_of_int j]);
fun Eijc ((i,j),c) = 
  if c = 1 then (mk_conj (Eij (i,j), Eij (j,i)))
  else if c = 2 then (mk_conj (mk_neg (Eij (i,j)), mk_neg (Eij (i,j))))
  else raise ERR "Eijc" "";

val ivar = mk_var ("i",``:num``);
val jvar = mk_var ("j",``:num``);
fun ijtm (i,j) = 
  mk_conj (mk_eq (ivar, numSyntax.term_of_int i), 
           mk_eq (jvar, numSyntax.term_of_int j));
fun ijtm2 (i,j) = mk_disj (ijtm (i,j),ijtm (j,i));
val abstm = list_mk_abs ([ivar,jvar], list_mk_disj (map ijtm2 edgel));
fun ijctm ((i,j),c) = 
  if c = 1 then mk_conj (ijtm (i,j),ijtm (j,i))
  else if c = 2 then mk_neg (mk_conj (ijtm (i,j),ijtm (j,i)))
  else raise ERR "ijctm" "";

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


(* -------------------------------------------------------------------------
   Proving the existence of the graph
   ------------------------------------------------------------------------- *)

fun read_graph () =
  let 
    val sl = readl (selfdir ^ "/r4524");
    fun f s = 
      map (fn x => if x = "F" then 2 else 1) (String.tokens Char.isSpace s);
    val ill = map f sl;
    val vv = Vector.fromList (map Vector.fromList ill);
    val m = mat_tabulate (Vector.length vv, (fn (i,j) => 
       if i = j then 0 else Vector.sub (Vector.sub (vv,i),j)));  
    val edgecl = mat_to_edgecl m
  in
    edgecl
  end;

val edgecl = read_graph ();
val edgel = map fst (filter (fn x => snd x = 1) edgecl);
val conjtm = list_mk_conj (map Eijc edgecl);
val existstm = mk_exists (E, conjtm);

val subtm = subst [{redex = E, residue = abstm}] conjtm;
fun create_exists () =
  let 
    val thm0 = REDEPTH_CONV BETA_CONV subtm;
    val thm1 = DECIDE ((rhs o concl) thm0);
    val thm2 = EQ_MP (SYM thm0) thm1;
    val thm3 = EXISTS (existstm,abstm) thm2;
  in
    thm3
  end;

val tm = ``(?(E: num -> num -> bool) . P E /\ !(E: num -> num -> bool) . P E ==> Q) ==> Q``;

val existsthm = create_exists ();

val thm2 = EQ_MP (SYM thm) thm1;

fun rpt_fun_type_im n ty imty =
  if n <= 0 then imty else mk_type ("fun",[ty,rpt_fun_type_im (n-1) ty imty]);

val P4 = mk_var ("P4",rpt_fun_type_im 4 ``:num`` bool);
val P5 = mk_var ("P5",rpt_fun_type_im 5 ``:num`` bool);

val instl = cartesian_productl (List.tabulate (4,fn _ => List.tabulate (24,I)));
fun P4app l = list_mk_comb (P4, map numSyntax.term_of_int l);
val tml = map P4app instl
val x4 = List.tabulate (4,X);
val x4less = map (fn x => numSyntax.mk_less (x, numSyntax.term_of_int 24))
 x4;
val P4all = list_mk_forall (x4, list_mk_imp (x4less,list_mk_comb (P4,x4)));

val P4dis = list_mk_imp (tml, P4all);


val tm = ``(x = 0 \/ x = 1 \/ x = 2) <=> x < 3``; 
val tm = ``(P 0 /\ P 1 /\ P 2) <=> (!x. x < 3 ==> P x)``; 

val thm = DECIDE ``0 < 1``;
val tm = ``P 0 <=> (0 < 1 ==> P 0)``;

val enum_thm = P (....)


