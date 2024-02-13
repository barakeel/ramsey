(* =========================================================================
   Compute a set of generalized graphs covering a set of graph
   uset stands for uncovered set.
   ========================================================================= *)
   
structure genv :> genv =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty syntax
val ERR = mk_HOL_ERR "genv"
type vleafs = int * int * (IntInf.int * int list) list  

val nauty_time = ref 0.0
val normalize_nauty = total_time nauty_time normalize_nauty

(* -------------------------------------------------------------------------
   Instantiating graphs
   ------------------------------------------------------------------------- *) 

fun all_subgraph depth mat =
  let
    val m = unzip_mat mat
    val size = mat_size m
    val subsize = size - depth
    val vertexl = List.tabulate (size,I)
    val perml = subsets_of_size subsize vertexl
    fun f x = mat_permute (m,subsize) (mk_permf x)
  in
    mk_fast_set IntInf.compare (map (zip_mat o normalize_nauty o f) perml)
  end

fun density m = number_of_blueedges (unzip_mat m);

fun create_cl mlsub = 
  let 
    val d = ref (dempty IntInf.compare) 
    fun f (m,subl) = 
      let fun g sub = d := dappend (sub,m) (!d) in
        app g subl
      end;
  in 
    app f mlsub; (dlist (!d)) 
  end

fun smallest_elem d = valOf (Redblackset.find (fn _ => true) d);

fun update_ko (keyd,orderd) (key,freq) =
  let 
    val aold as (a,b,c) = dfind key (!keyd)
    val anew = (a-freq,b,c)
  in
    orderd := eadd anew (erem aold (!orderd));  
    keyd := dadd key anew (!keyd)
  end

fun loop (keyd,orderd) pd cd uset result =
  if elength uset <= 0 then rev result else
  let
    val (sc1,sc2,bestc) = smallest_elem (!orderd)
    val _ = log (its (elength uset) ^ ": " ^ its sc1 ^ " " ^ its sc2)
    val pl1 = dfind bestc cd
    val pl2 = filter (fn x => emem x uset) pl1
    val cfreql0 = List.concat (map (fn x => dfind x pd) pl2)
    val cfreql1 = dlist (count_dict (dempty IntInf.compare) cfreql0)
    val _ = app (update_ko (keyd,orderd)) cfreql1
    val newuset = ereml pl2 uset
    val newresult = (bestc,pl2) :: result
  in
    loop (keyd,orderd) pd cd newuset newresult
  end;

fun inv_cmp cmp (a,b) = cmp (b,a);
val compare_score = triple_compare (inv_cmp Int.compare) (inv_cmp Int.compare)
  IntInf.compare;

fun compute_cover depth ml = 
  let
    val uset = enew IntInf.compare ml
    val _ = log "creating subgraphs"
    val mlsub = map_assoc (all_subgraph depth) ml
    val _ = log "parent dict"
    val pd = dnew IntInf.compare mlsub
    val _ = log "children dict"
    val cd = dnew IntInf.compare (create_cl mlsub)
    val _ = log "computing density"
    val keyl = map (fn (a,b) => (a, (length b, density a,a))) (dlist cd);
    val keyd = ref (dnew IntInf.compare keyl)
    val orderd = ref (enew compare_score (map snd keyl));
  in
    loop (keyd,orderd) pd cd uset []
  end; 




end (* struct *)






