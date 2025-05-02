(* =========================================================================
   Compute a set of generalized graphs covering a set of graph
   uset stands for uncovered set.
   ========================================================================= *)
   
structure gen :> gen =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty syntax enum sat
val ERR = mk_HOL_ERR "gen"
type vleafs = int * int * (IntInf.int * int list) list  

(* -------------------------------------------------------------------------
   Global parameters
   ------------------------------------------------------------------------- *) 

val maxhole = ref 8 
val exponent = ref 1.0
val mincover = ref (1.0 / 8.0)
val select_number1 = ref 240
val select_number2 = ref 120
val select_basic = ref false


(* -------------------------------------------------------------------------
   Convert colored edges to int
   ------------------------------------------------------------------------- *) 

fun enc_color (x,c) = if c = 1 then 2 * x else 2 * x + 1;
fun enc_edgec (e,c) = enc_color (edge_to_var e,c);
fun dec_edgec x = (var_to_edge (x div 2), (x mod 2) + 1);
fun opposite (e,x) = (e,3 - x)
fun opposite_v v = (enc_edgec o opposite o dec_edgec) v

(* -------------------------------------------------------------------------
   Getting all_leafs of 
   ------------------------------------------------------------------------- *) 

fun all_leafs_wperm uset m =
  let
    val edgel = all_holes m
    val coloringltop = all_coloring edgel
    fun loop d e coloringl = case coloringl of 
        [] => (d,e)
      | coloring :: cont =>
        let 
          val child = apply_coloring m coloring     
          val (normm,perm) = normalize_nauty_wperm child
          val normi = zip_mat normm
          val newe = eadd normi e
        in
          if emem normi uset
          then loop (dadd normi perm d) newe cont
          else loop d newe cont
        end
  in
    loop (dempty IntInf.compare) (eempty IntInf.compare) coloringltop 
  end

(* -------------------------------------------------------------------------
   Scoring generalizations: lower number is better.
   ------------------------------------------------------------------------- *)

val clique35 = [(1,1),(2,1),(2,2),(3,2),(4,2)]
val clique44 = [(3,1),(2,1),(3,2),(2,2),(1,2)]

fun number_of_cliques m (n,color) =
  let 
    val vl = List.tabulate (mat_size m, I)
    val cliquel = subsets_of_size n vl
    fun is_uniform x = 
      let 
        val edgel = all_pairs x 
        fun test (i,j) = mat_sub (m,i,j) = color 
      in
        all test edgel
      end
  in
    ((n,color), Real.fromInt (length (filter is_uniform cliquel)))
  end

fun get_stats35 m = map (number_of_cliques m) clique35
fun get_stats44 m = map (number_of_cliques m) clique44

fun get_average35 enum =
  let val l = map (map snd o get_stats35 o unzip_mat) enum in
    combine (clique35, map average_real (list_combine l))
  end

fun get_average44 enum =
  let val l = map (map snd o get_stats44 o unzip_mat) enum in
    combine (clique44, map average_real (list_combine l))
  end


(* 
load "gen"; open kernel enum gen;
range (5,13, fn k => (k, get_average35 (read_enum k (3,5))));
range (4,17, fn k => (k, get_average44 (read_enum k (4,4))));
*)


val average35l =
    [
     (5,
     [((1, 1), 5.0), ((2, 1), 3.538461538), ((2, 2), 6.461538462),
      ((3, 2), 2.769230769), ((4, 2), 0.3846153846)]),
    (6,
     [((1, 1), 6.0), ((2, 1), 5.3125), ((2, 2), 9.6875), ((3, 2), 5.25),
      ((4, 2), 0.84375)]),
    (7,
     [((1, 1), 7.0), ((2, 1), 7.267605634), ((2, 2), 13.73239437),
      ((3, 2), 9.309859155), ((4, 2), 1.929577465)]),
    (8,
     [((1, 1), 8.0), ((2, 1), 9.61452514), ((2, 2), 18.38547486),
      ((3, 2), 14.84916201), ((4, 2), 3.720670391)]),
    (9,
     [((1, 1), 9.0), ((2, 1), 12.10689655), ((2, 2), 23.89310345),
      ((3, 2), 22.55517241), ((4, 2), 6.55862069)]),
    (10,
     [((1, 1), 10.0), ((2, 1), 15.01916933), ((2, 2), 29.98083067),
      ((3, 2), 32.48242812), ((4, 2), 10.93610224)]),
    (11,
     [((1, 1), 11.0), ((2, 1), 18.36190476), ((2, 2), 36.63809524),
      ((3, 2), 44.88571429), ((4, 2), 17.4)]),
    (12,
     [((1, 1), 12.0), ((2, 1), 22.16666667), ((2, 2), 43.83333333),
      ((3, 2), 59.33333333), ((4, 2), 25.66666667)]),
    (13,
     [((1, 1), 13.0), ((2, 1), 26.0), ((2, 2), 52.0), ((3, 2), 78.0),
      ((4, 2), 39.0)])];
 
val average44l =  
   [(4,
     [((3, 1), 0.4444444444), ((2, 1), 3.0), ((3, 2), 0.4444444444),
      ((2, 2), 3.0), ((1, 2), 4.0)]),
    (5,
     [((3, 1), 1.125), ((2, 1), 5.0), ((3, 2), 1.125), ((2, 2), 5.0),
      ((1, 2), 5.0)]),
    (6,
     [((3, 1), 2.095238095), ((2, 1), 7.5), ((3, 2), 2.095238095),
      ((2, 2), 7.5), ((1, 2), 6.0)]),
    (7,
     [((3, 1), 3.571823204), ((2, 1), 10.5), ((3, 2), 3.571823204),
      ((2, 2), 10.5), ((1, 2), 7.0)]),
    (8,
     [((3, 1), 5.541125541), ((2, 1), 14.0), ((3, 2), 5.541125541),
      ((2, 2), 14.0), ((1, 2), 8.0)]),
    (9,
     [((3, 1), 8.186994082), ((2, 1), 18.0), ((3, 2), 8.186994082),
      ((2, 2), 18.0), ((1, 2), 9.0)]),
    (10,
     [((3, 1), 11.59094941), ((2, 1), 22.5), ((3, 2), 11.59094941),
      ((2, 2), 22.5), ((1, 2), 10.0)]),
    (11,
     [((3, 1), 15.91500597), ((2, 1), 27.5), ((3, 2), 15.91500597),
      ((2, 2), 27.5), ((1, 2), 11.0)]),
    (12,
     [((3, 1), 21.30271549), ((2, 1), 33.0), ((3, 2), 21.30271549),
      ((2, 2), 33.0), ((1, 2), 12.0)]),
    (13,
     [((3, 1), 27.89530843), ((2, 1), 39.0), ((3, 2), 27.89530843),
      ((2, 2), 39.0), ((1, 2), 13.0)]),
    (14,
     [((3, 1), 35.81875306), ((2, 1), 45.5), ((3, 2), 35.81875306),
      ((2, 2), 45.5), ((1, 2), 14.0)]),
    (15,
     [((3, 1), 45.6015625), ((2, 1), 52.5), ((3, 2), 45.6015625),
      ((2, 2), 52.5), ((1, 2), 15.0)]),
    (16,
     [((3, 1), 56.0), ((2, 1), 60.0), ((3, 2), 56.0), ((2, 2), 60.0),
      ((1, 2), 16.0)]),
    (17,
     [((3, 1), 68.0), ((2, 1), 68.0), ((3, 2), 68.0), ((2, 2), 68.0),
      ((1, 2), 17.0)])];

val average35v = Vector.fromList 
  (List.tabulate (5,fn _ => NONE) @ map (SOME o snd) average35l);
val average44v = Vector.fromList 
  (List.tabulate (4,fn _ => NONE) @ map (SOME o snd) average44l);

fun difficulty stats35 stats45 =
  let 
    val l = combine (stats35,stats45)
    fun f (((n1,_),r1),((n2,_),r2)) = 
      r1 * r2 * (1.0 / Math.pow (2.0, Real.fromInt (n1 * n2)))
  in
    sum_real (map f l)
  end
  
fun difficulty_pair (m1,m2) =
  difficulty (get_stats35 (unzip_mat m1)) (get_stats44 (unzip_mat m2)) 

fun poke_hole leaf edgel = 
  let 
    val newleaf = mat_copy leaf
    fun f (i,j) = mat_update_sym (newleaf,i,j,0)
    val _ = app f edgel
  in
    newleaf
  end

fun scorem (bluen,redn) m =
  if (bluen,redn) = (3,5)
  then difficulty 
    (get_stats35 m) 
    (valOf (Vector.sub (average44v,(24 - mat_size m))))
  else if (bluen,redn) = (4,4) 
  then difficulty 
    (valOf (Vector.sub (average35v,(24 - mat_size m)))) 
    (get_stats44 m)
  else raise ERR "scorem" ""

fun score_leaf br leaf edgel = scorem br (poke_hole leaf edgel)

fun scorev br leaf result v =
  let 
    val edgel = map (fst o dec_edgec o #1) result
    val edge = fst (dec_edgec v)
  in
    score_leaf br leaf (edge :: edgel)
  end

fun score_leafv_diff br (leafi,vl) =
  let 
    val edgel = map (fst o dec_edgec o #1) vl 
    val diffn = score_leaf br (unzip_mat leafi) edgel
  in
    Math.pow (diffn,!exponent) 
  end

fun score_leafv diffd br (leafi,vl) =
  let
    val cover = List.concat (map (map fst o #3) vl)
    val covern = Real.fromInt (elength (enew IntInf.compare cover))
  in
    if !select_basic 
    then covern
    else dfind (leafi,map #1 vl) diffd
  end
  
(* -------------------------------------------------------------------------
   Cover
   ------------------------------------------------------------------------- *)

fun init_sgen size (bluen,redn) = 
  let
    val clauses1 = sat.ramsey_clauses size (bluen,redn)
    val clauses2 = map (map enc_color) clauses1
    val clausev = Vector.fromList clauses2;
    val claused = dnew (list_compare Int.compare) (number_snd 0 clauses2)
    fun g clause = map_assoc (fn _ => clause) clause
    val clauses3 = List.concat (map g clauses2)
    val clauses4 = dlist (dregroup Int.compare clauses3)
    val clauses5 = map_snd (map (fn x => dfind x claused)) clauses4
    val clauses6 = map_snd (dict_sort Int.compare) clauses5
    val varv = Vector.fromList (map snd clauses6)
  in
    (varv,clausev)
  end;
  
fun build_parent leaf edgel = 
  let
    val parent = mat_copy leaf
    fun f (i,j) = mat_update_sym (parent,i,j,0)
    val _ = app f edgel
  in
    parent
  end;     
  
fun build_sibling leaf edgel (itop,jtop) = 
  let
    val sibling = build_parent leaf edgel
    val oppc = 3 - mat_sub (leaf,itop,jtop)
    val _ = mat_update_sym (sibling,itop,jtop,oppc)
  in
    sibling
  end

fun concat_cpermll (leafi,vleafsl) = 
  let val idperm = List.tabulate (mat_size (unzip_mat leafi),I) in
    mk_fast_set (fst_compare IntInf.compare)
      ((leafi,idperm) :: List.concat (map #3 vleafsl))
  end

(* each entry of varv contains the list of clause the variable i occurs in *)
fun sgeneralize (bluen,redn) uset leafi =
  let
    val leaf = unzip_mat leafi
    val size = mat_size leaf
    val (varv,clausev) = init_sgen size (bluen,redn) 
    val sizev = Vector.map (fn x => length x - 1) clausev
    val inita = Array.array (Vector.length clausev,0)    
    fun update_numbera a v = 
      let 
        val il = Vector.sub (varv,v) 
        fun g i = Array.update (a,i, Array.sub(a,i) + 1) 
      in
        app g il
      end
    val edgecl = mat_to_edgecl leaf
    val _ = app (update_numbera inita) (map enc_edgec edgecl)
    fun try () = 
      let
        val locala = Array.tabulate 
          (Array.length inita, fn i => Array.sub (inita,i))
        val vlopp = shuffle (map (enc_edgec o opposite) edgecl)
        fun test v = 
          let val clausel = Vector.sub (varv,v) in
            all (fn x => Array.sub (locala, x) < Vector.sub(sizev,x)) clausel
          end
        fun sgen_loop vl result = 
          if length result >= (!maxhole) then rev result else
          case if !select_basic then vl else
                map fst (dict_sort compare_rmax 
                (map_assoc (scorev (bluen,redn) leaf result) vl)) 
          of
            [] => rev result
          | v :: rem => 
            let 
              val edgel = map (fst o dec_edgec o #1) result
              val edge = fst (dec_edgec v)
              val sibling = build_sibling leaf edgel edge
              val (d,e) = all_leafs_wperm uset sibling
              val maxn = elength e
            in
              if Real.fromInt (dlength d) / Real.fromInt maxn >= (!mincover)
              then (update_numbera locala v;
                    sgen_loop (filter test rem) ((v,maxn,dlist d) :: result)) 
              else sgen_loop rem result
            end   
      in
        sgen_loop (filter test vlopp) []
      end 
  in  
    try ()
  end;

(* -------------------------------------------------------------------------
   Test for presence of cliques
   ------------------------------------------------------------------------- *)

(* assumes that we are not removing variable twice *)
fun decr_numbera a varv v = 
  let 
    val il = Vector.sub (varv,v) 
    fun g i = Array.update (a,i, if Array.sub(a,i) - 1 < 0 then raise ERR
      "decr_numbera" "" else Array.sub(a,i) - 1) 
  in
    app g il
  end
  
fun incr_numbera a varv v = 
  let 
    val il = Vector.sub (varv,v) 
    fun g i = Array.update (a,i, Array.sub(a,i) + 1) 
  in
    app g il
  end

fun can_increase a sizev clause =
  Array.sub (a, clause) + 1 < Vector.sub (sizev,clause)

fun can_increase2 a sizev clause =
  Array.sub (a, clause) + 2 < Vector.sub (sizev,clause)

fun test_v2 sizev a varv (v1,v2) =
  let
    val _ = decr_numbera a varv v1
    val _ = decr_numbera a varv v2
    val v1o = opposite_v v1
    val v2o = opposite_v v2
    val vvl = [(v1,v2o),(v1o,v2),(v1o,v2o)]
    fun test_vv (va,vb) = 
      let
        val clausela = Vector.sub (varv,va)
        val clauselb = Vector.sub (varv,vb)
        (* slow intersection: probably do and undo is faster and
           catch error *)
        val da = enew Int.compare clausela
        val clauselab = filter (fn x => emem x da) clauselb
      in
        all (can_increase a sizev) clausela andalso
        all (can_increase a sizev) clauselb andalso
        all (can_increase2 a sizev) clauselab        
      end
    val vvl' = filter test_vv vvl
    (* restore *)
    val _ = incr_numbera a varv v1 
    val _ = incr_numbera a varv v2
  in
    if null vvl' then NONE else SOME ((v1,v2) :: vvl')
  end

fun test_allpairs sizev a varv edgecgenl =
  let 
    val vl = map enc_edgec edgecgenl
    val vvl = all_pairs vl
    val vvll = List.mapPartial (test_v2 sizev a varv) vvl
    fun f (v1,v2) = string_of_edgec (dec_edgec v1) ^ "|" ^ 
                    string_of_edgec (dec_edgec v2)
    fun g x = print_endline (String.concatWith " " (map f x))
  in
    print_endline (its (length vvll) ^ " gen2");
    app g (first_n 10 vvll)
  end



(* -------------------------------------------------------------------------
   Inefficient model counter for graphs
   ------------------------------------------------------------------------- *)

fun contradict_clause model clause =
  all (fn ((i,j),c) => mat_sub (model,i,j) = c) clause

fun contradict_clausel clausel model = 
  exists (contradict_clause model) clausel

fun model_counter msize edgel clausel =
  let 
    val modell1 = cartesian_productl (map (fn x => [(x,1),(x,2)]) edgel) 
    val modell2 = map (edgecl_to_mat msize) modell1 
    val modell3 = filter (not o contradict_clausel clausel) modell2 
  in
    length modell3
  end
  handle Subscript => raise ERR "model_counter" ""

(* -------------------------------------------------------------------------
   Cover for transverse edges
   ------------------------------------------------------------------------- *)

fun conflict_clauses numbera sizev varv v =
  let 
    val clausel = Vector.sub (varv,v) 
    fun test x = Array.sub (numbera, x) + 1 >= Vector.sub(sizev,x)
  in
    filter test clausel
  end
  
fun conflict_clauses2 numbera sizev varv (v1,v2) =
  let 
    val clausel1 = Vector.sub (varv,v1)
    val clausel2 = Vector.sub (varv,v2)
    val clauseu = mk_fast_set Int.compare (clausel1 @ clausel2)
    val d2 = enew Int.compare clausel2
    val clausei = filter (fn x => emem x d2) clausel1
    fun test1 x = Array.sub (numbera,x) + 1 >= Vector.sub(sizev,x)
    fun test2 x = Array.sub (numbera,x) + 2 >= Vector.sub(sizev,x)
  in
    filter test1 clauseu @ filter test2 clausei 
  end  

fun test_allsingleton size holeedgel prevccl numbera sizev varv clausev vlopp =
  let
    val _ = print_endline "compute conflicts"
    val vccl = map_assoc (conflict_clauses numbera sizev varv) vlopp
    fun score_edge (v,ccl) = 
      let
        val (holedge,_) = dec_edgec v
        val clausel = map (fn x => Vector.sub (clausev,x)) 
          (mk_fast_set Int.compare (prevccl @ ccl)) 
        val newholeedgel = holedge :: holeedgel
        val holed = enew edge_compare newholeedgel
        val clausel' = map (filter (fn (x,_) => emem x holed)) clausel 
      in
        model_counter size newholeedgel clausel'
      end
    val vccli = map_assoc score_edge vccl
    fun f ((v,ccl),i) = 
      print_endline (
        (string_of_edgec o dec_edgec) v ^ " " ^
        its (length ccl) ^ " " ^
        its i
      )
  in
    print_endline ("edge conflicts cover");
    app f vccli
  end
  
fun best_vlopp size holeedgel prevccl numbera sizev varv clausev vlopp =
  let
    val vccl = map_assoc (conflict_clauses numbera sizev varv) vlopp
    fun score_edge (v,ccl) = 
      let
        val (holedge,_) = dec_edgec v
        val newccl = mk_fast_set Int.compare (prevccl @ ccl)
        val clausel = map (fn x => Vector.sub (clausev,x)) newccl
        val newholeedgel = holedge :: holeedgel
        val holed = enew edge_compare newholeedgel
        val clausel' = map (filter (fn (x,_) => emem x holed)) clausel
      in
        ((v,newccl), model_counter size (holedge :: holeedgel) clausel')
      end
    val vccli = map score_edge vccl
    val ((v,finalccl),covern) = hd (dict_sort compare_imax vccli)
    val _ = print_endline (
      its (length holeedgel + 1) ^ ":  " ^ 
      string_of_edgec (dec_edgec v) ^ " " ^
      its (length (finalccl)) ^ " " ^ its covern
      )
  in
    (v,finalccl)
  end
  
fun best_vvlopp size holeedgel prevccl numbera sizev varv clausev vlopp =
  let
    val vccl = map_assoc (conflict_clauses2 numbera sizev varv) 
      (all_pairs vlopp)
    fun score_edge ((v1,v2),ccl) = 
      let
        val (edge1,edge2) = (fst (dec_edgec v1), fst (dec_edgec v2))
        val newccl = mk_fast_set Int.compare (prevccl @ ccl)
        val clausel = map (fn x => Vector.sub (clausev,x)) newccl
        val newholeedgel = edge1 :: edge2 :: holeedgel
        val holed = enew edge_compare newholeedgel
        val clausel' = map (filter (fn (x,_) => emem x holed)) clausel
      in
        (((v1,v2),newccl), model_counter size newholeedgel clausel')
      end
    val vccli = map score_edge vccl
    val ((vv,finalccl),covern) = hd (dict_sort compare_imax vccli)
    val _ = print_endline (
      its (length holeedgel + 1) ^ ":  " ^ 
      string_of_edgec (dec_edgec (fst vv)) ^ " " ^
      string_of_edgec (dec_edgec (snd vv)) ^ " " ^
      its (length (finalccl)) ^ " " ^ its covern
      )
  in
    (vv,finalccl)
  end  
  
(*
todo: make a incremental model counter for faster counting
(this kind of does not work unless components are sperated)
(maybe don't care about the exact number)
(maybe remove two at a time)

fun conflict_var numbera v = 
  let 
    val clausel = Vector.sub (varv,v) 
    fun has_conflict x = Array.sub (numbera, x) + 1 >= Vector.sub(sizev,x)
  in
    filter has_conflict clausel
  end

select the highest var with highest model count
*)

fun reduce_clause mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 
        then reduce_clause mat (lit :: acc) m
      else if color = newcolor 
        then reduce_clause mat acc m else NONE
    end

fun ramsey_clauses_mat (bluen,redn) mat =
  List.mapPartial (reduce_clause mat []) 
    (ramsey_clauses_bare (mat_size mat) (bluen,redn))
  handle Subscript => raise ERR "ramsey_clauses_mat" ""

val extra_clausel = ref ([]: ((int * int) * int) list list)
  
fun init_sgen_reduce (bluen,redn) mat = 
  let
    val size = mat_size mat
    val vsize = size * (size - 1) (* div 2 times 2 *)
    (* val clauses0 = ramsey_clauses_mat (bluen,redn) mat @ !extra_clausel *)
    val clauses0 = 
      map (map_fst var_to_edge) (sat.ramsey_clauses size (bluen,redn)) @ 
      !extra_clausel
    val clausev = Vector.fromList clauses0
    val clauses2 = map (map enc_edgec) clauses0
    val claused = dnew (list_compare Int.compare) (number_snd 0 clauses2)
    fun g clause = map_assoc (fn _ => clause) clause
    val clauses3 = List.concat (map g clauses2)
    val clauses4 = dlist (dregroup Int.compare clauses3)
    val clauses5 = map_snd (map (fn x => dfind x claused)) clauses4
    val clausesd = dnew Int.compare clauses5
    val varv = Vector.tabulate (vsize, fn x => (dfind x clausesd
      handle NotFound => []))
  in
    (varv,clausev)
  end;

(* 
todo: rank all variables by the number of conflict 

1) write the function for the ranking of edges.
4) prefer edges that maximize the size of the cover (greedily)
   tie-break minimum number of conflict
   (maybe this will build too large clauses)
   (maybe limit the size of clauses to 2 or 3).
*)

(*
fun rank_var sizev a varv var =
  let 
    
    val vlopp = map (enc_edgec o opposite) edgecgenl
    fun f (v,cn) = 
      print_endline (string_of_edgec (dec_edgec v) ^ ": " ^ its cn)
    val l = dict_sort compare_imin (map_assoc conflicts vlopp)   
  in
    print_endline ("variable: conflict number");
    app f l
  end
*)

fun gen_simple (bluen,redn) edgecgenl nhole parenti leafi ntry =
  let
    val leaf = unzip_mat leafi
    val parent = unzip_mat parenti
    val size = mat_size leaf
    (* initalization *)
    val _ = print_endline "initialization"
    val (varv,clausev) = init_sgen_reduce (bluen,redn) parent
    val sizev = Vector.map (fn x => length x) clausev
    val inita = Array.array (Vector.length clausev,0)
    val holea = Array.array (Vector.length clausev,[])
    (* val baseedgecl = list_diff (mat_to_edgecl leaf) (mat_to_edgecl parent) *)
    val _ = app (incr_numbera inita varv) (map enc_edgec (mat_to_edgecl leaf))
    val vlopp = map (enc_edgec o opposite) edgecgenl
    val holeedgel = ref []
    val prevccl = ref []
    (* val _ = test_allsingleton size (!holeedgel) (!prevccl) 
        inita sizev varv clausev vlopp *)
    (* generalization loop *)
    fun gen_loop () = 
      let
        val locala = Array.tabulate 
          (Array.length inita, fn i => Array.sub (inita,i))
        fun test v = 
          let val clausel = Vector.sub (varv,v) in
            all 
            (fn x => Array.sub (locala, x) + 1 < Vector.sub(sizev,x)) clausel
          end
        fun sgen_loop vl result = 
          if length result >= nhole then rev result else
          case vl of
            [] => rev result
          | _ => 
            let 
              val ((v1,v2),ccl) = best_vvlopp size (!holeedgel) (!prevccl) 
                locala sizev varv clausev vl
              val (edge1,edge2) = (fst (dec_edgec v1),fst (dec_edgec v2))
              val _ = prevccl := mk_fast_set Int.compare (ccl @ !prevccl)
              val _ = holeedgel := edge1 :: edge2 :: !holeedgel
              val newvl = filter (fn x => x <> v1 andalso x <> v2) vl
              val newresult = edge1 :: edge2 :: result
            in
              incr_numbera locala varv v1; 
              incr_numbera locala varv v2;
              sgen_loop newvl newresult
            end   
      in
        sgen_loop vlopp []
      end 
    val rl = List.tabulate (ntry, fn _ => gen_loop ())
    val rli = map_assoc length rl
  in  
    fst (hd (dict_sort compare_imax rli))
  end;

(* -------------------------------------------------------------------------
   Finding generalizations not overlapping too much
   ------------------------------------------------------------------------- *)
   
fun sgen_worker ((bluen,redn),uset) leafi =
  let
    val vleafsl = sgeneralize (bluen,redn) uset leafi in
    (leafi, vleafsl)
  end

fun write_infset file ((a,b),set) = writel file 
  (its a :: its b :: map infts (elist set))
fun read_infset file = case readl file of
  sa :: sb :: m => ((string_to_int sa,string_to_int sb), 
                    enew IntInf.compare (map stinf m))
  | _ => raise ERR "read_infset" ""
 
fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))

fun string_of_cperm (c,perm) = 
  String.concatWith "_" (infts c :: map its perm)

fun cperm_of_string s = case String.tokens (fn x => x = #"_") s of
    a :: m => (stinf a, map string_to_int m)
  | _ => raise ERR "cperm_of_string" ""

fun string_of_vleafs (v,maxn,cperml) = 
  String.concatWith " " (its v :: its maxn :: map string_of_cperm cperml)

fun vleafs_of_string s = case String.tokens Char.isSpace s of
    a :: b :: m => (string_to_int a, string_to_int b, map cperm_of_string m)
  | _ => raise ERR "vleafs_of_string" ""

fun write_result file (leafi,vleafsl)  =
  writel file (infts leafi :: map string_of_vleafs vleafsl)

fun read_result file = case readl file of 
    a :: m => (stinf a, map vleafs_of_string m)
  | _ => raise ERR "read_result" ""

val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
  IntInf.int * vleafs list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "gen.genspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir),
     "gen.maxhole := " ^ its (!maxhole),
     "gen.exponent := " ^ rts (!exponent)
    ] 
    ^ ")"),
  function = sgen_worker,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = write_result,
  read_result = read_result
  }

fun remove_vleafsl_aux uset (leafi,vleafsl) acc = case vleafsl of
    [] => SOME (leafi, rev acc)
  | (v,maxn,cperml) :: m =>  
    let val newcperml = filter (fn x => emem (fst x) uset) cperml in
      if Real.fromInt (length newcperml) / Real.fromInt maxn >= !mincover 
      then remove_vleafsl_aux uset (leafi,m) ((v,maxn,newcperml) :: acc)
      else NONE
    end

fun remove_vleafsl uset (leafi,vleafsl) = 
  if not (emem leafi uset) 
  then NONE 
  else remove_vleafsl_aux uset (leafi,vleafsl) []

fun update_uset diffd br selectn pl (uset,result) =
  if elength uset <= 0 orelse 
     null pl orelse 
     selectn >= !select_number2 
     then (uset,result) else
  let 
    val l1 = map_assoc (score_leafv diffd br) pl
    val l2 = dict_sort compare_rmax l1
    val (leafi,vleafsl) = fst (hd l2) 
    val cperml = concat_cpermll (leafi,vleafsl)
    val keyl = map fst cperml
    val newuset = ereml keyl uset
    val edgel = map (fst o dec_edgec o #1) vleafsl
    val pari = zip_mat (build_parent (unzip_mat leafi) edgel)
    val newresult = (pari,cperml) :: result
    val newpl = List.mapPartial (remove_vleafsl newuset) pl
    val _ = log ("Covering " ^ its (length cperml) ^ " graphs (" ^ 
                 its (elength newuset) ^ " remaining)" ^
                 " at depth " ^ its (length vleafsl))
  in
    update_uset diffd br (selectn + 1) newpl (newuset,newresult)
  end

fun loop_scover_para ncore (bluen,redn) uset result = 
  if elength uset <= 0 then rev result else
  let
    val n = Int.min (!select_number1, elength uset)
    val ul = random_subset n (elist uset)
    val n' = Int.min (n,ncore)
    val param = ((bluen,redn),uset)
    val _ = clean_dir (selfdir ^ "/parallel_search")
    val pl = smlParallel.parmap_queue_extern n' genspec param ul
    val diffl1 = map_assoc (score_leafv_diff (bluen,redn)) pl
    val diffl2 = map (fn ((a,b),c) => ((a, map #1 b),c)) diffl1
    val diffd = dnew (cpl_compare IntInf.compare (list_compare Int.compare))
      diffl2
    val (newuset,newresult) = update_uset diffd (bluen,redn) 0 pl (uset,result)
  in
    loop_scover_para ncore (bluen,redn) newuset newresult
  end


fun check_cover cover uset =
  let 
    val _ = print_endline "checking cover" 
    val instl = mk_fast_set IntInf.compare 
      (map fst (List.concat (map snd cover)))
  in
    if elist uset = instl 
    then ()
    else raise ERR "check_cover" ""
  end

fun compute_scover_para ncore size (bluen,redn) = 
  let
    val id = its bluen ^ its redn ^ its size
    val file = selfdir ^ "/enum/enum" ^ id
    val uset = enew IntInf.compare (map stinf (readl file));
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val cover = loop_scover_para ncore (bluen,redn) uset []
    val _ = check_cover cover uset
  in
    cover
  end

(* -------------------------------------------------------------------------
   Generalizations I/O
   ------------------------------------------------------------------------- *)

fun read_cover size (bluen,redn) =
  let 
    val file = selfdir ^ "/gen/gen" ^ 
      its bluen ^ its redn ^ its size
    val sl = readl file
    fun f s = 
      let 
        val sl1 = String.tokens Char.isSpace s
        val sll2 = map (String.tokens (fn x => x = #"_")) (tl sl1)
        fun g sl2 = (stinf (hd sl2), map string_to_int (tl sl2))
      in
        (stinf (hd sl1), map g sll2)
      end
  in
    map f sl
  end
  
fun read_par size (bluen,redn) =
  let 
    val file = selfdir ^ "/gen/gen" ^ 
      its bluen ^ its redn ^ its size
    val sl = readl file
    fun f s = 
      let val sl1 = String.tokens Char.isSpace s in
        stinf (hd sl1)
      end
  in
    map f sl
  end

fun write_cover size (bluen,redn) cover = 
  let 
    val dir = selfdir ^ "/gen"
    val _ = mkDir_err dir
    val file = dir ^ "/gen" ^ its bluen ^ its redn ^ its size
    fun f (p,cperml) = 
      let fun g (c,perm) = infts c ^ "_" ^ 
        String.concatWith "_" (map its perm) 
      in
        String.concatWith " " (infts p :: map g cperml)
      end
  in
    mkDir_err dir;
    writel file (map f cover)
  end  

(* -------------------------------------------------------------------------
   Generalization main function
   ------------------------------------------------------------------------- *)

fun gen (bluen,redn) (minsize,maxsize) =  
  let
    fun f size =
      let
        val _ = print_endline ("size " ^ its size)
        val cover = compute_scover_para ncore size (bluen,redn)
      in
        write_cover size (bluen,redn) cover
      end  
  in
    ignore (range (minsize,maxsize,f))
  end
  

(*
load "gen"; open sat aiLib kernel graph gen;

clean_dir (selfdir ^ "/gen");
maxhole := 10;
select_basic := true;
select_number1 := 313;
select_number2 := 1;
val (_,t35) = add_time (gen (3,5)) (12,12);
select_number1 := 1000;
select_number2 := 100;
val (_,t44) = add_time (gen (4,4)) (14,14);

*)


end (* struct *)






