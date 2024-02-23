(* =========================================================================
   Compute a set of genralized graphs covering a set of graph
   uset stands for uncovered set.
   ========================================================================= *)
   
structure genb :> genb =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty syntax
val ERR = mk_HOL_ERR "genb"

val sample_number = ref 1000
val max_hole = ref 8
(* load "graph"; open aiLib graph"; val m = random_full_mat 12; *)

(* -------------------------------------------------------------------------
   Instantiating graphs
   ------------------------------------------------------------------------- *) 

fun all_leafs_wperm_aux uset m edgel =
  let
    val coloringltop = all_coloring edgel
    val d = ref (dempty IntInf.compare)
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

fun all_leafs_wperm uset m = all_leafs_wperm_aux uset m

fun all_leafs_aux uset leafd m coloringl = case coloringl of 
    [] => leafd
  | coloring :: cont =>
    let
      val normi = zip_mat (normalize_nauty (apply_coloring m coloring))
      val newleafd = if emem normi uset then eadd normi leafd else leafd
    in
      all_leafs_aux uset newleafd m cont
    end;
 
fun all_leafs uset m edgel = 
  let 
    val coloringl = all_coloring edgel
    val leafd = eempty IntInf.compare
  in 
    all_leafs_aux uset leafd m coloringl
  end

(* -------------------------------------------------------------------------
   Generalize one graph with respect to an uncovered set
   ------------------------------------------------------------------------- *)

fun gen_one uset m prefix nhole (bestedgel,bestsc) =
  let
    val edgel = random_subset nhole (all_edges (mat_size m))
    val sc = elength (all_leafs uset m (prefix @ edgel))
  in
    if sc > !bestsc
    then (bestedgel := edgel; bestsc := sc)
    else ()
  end
  
fun gen_multi uset m prefix nhole (bestedgel,bestsc) =
  let fun f n = gen_one uset m prefix nhole (bestedgel,bestsc) in
    List.tabulate (!sample_number,f)
  end
  
fun gen_stages_aux uset m prefix nhole (bestedgel,bestsc) =
  if nhole <= 0 then prefix else
  let 
    val _ = gen_multi uset m prefix nhole (bestedgel,bestsc)
    val edge = random_elem (!bestedgel) 
    val _ = bestedgel := filter (fn x => x <> edge) (!bestedgel)
  in
    gen_stages_aux uset m (edge :: prefix) (nhole - 1) (bestedgel,bestsc)
  end
  
fun gen_stages uset m =
  let
    val bestedgel = ref []
    val bestsc = ref ~2
  in
    gen_stages_aux uset m [] (!max_hole) (bestedgel,bestsc)
  end
 
fun greedy_cover_aux uset result =
  if elength uset <= 0 then rev result else
  let 
    val _ = log ("uset: " ^ its (elength uset))
    val m = unzip_mat (random_elem (elist uset)) 
    val (edgel,t) = add_time (gen_stages uset) m
    val _ = log ("gen_stages: " ^ rts_round 4 t)
    val leafd = all_leafs uset m edgel
    val newuset = ereml (elist leafd) uset
    val newresult = (m,edgel) :: result
  in
    greedy_cover_aux newuset newresult
  end
  
fun greedy_cover uset = greedy_cover_aux uset []
    
  
(*
load "genb"; open aiLib kernel graph genb;

val bluen = 4;
val redn = 4;
val size = 9;
val id = its bluen ^ its redn ^ its size;
val file = selfdir ^ "/enum/enum" ^ id;
val _ = max_hole := 8;
val _ = sample_number := 200;
val uset = enew IntInf.compare (map stinf (readl file));

val cover = greedy_cover uset;
elength uset;
length cover;


val edgel = greedy_cover uset;

*)

(* 
(* safety check *)
load "gen"; load "enum"; open sat aiLib kernel graph enum gen;
val cover3510 = read_cover 10 (3,5);
val inst3510 =
  mk_fast_set IntInf.compare (map fst (List.concat (map snd cover3510)));
val inst3510' = read_enum 10 (3,5);
list_compare IntInf.compare (inst3510,inst3510');

val cover4410 = read_cover 10 (4,4);
val inst4410 =
  mk_fast_set IntInf.compare (map fst (List.concat (map snd cover4410)));
val inst4410' = read_enum 10 (4,4);
list_compare IntInf.compare (inst4410,inst4410');
*)

end (* struct *)






