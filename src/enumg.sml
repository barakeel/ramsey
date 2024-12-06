structure enumg :> enumg =
struct   

open HolKernel aiLib kernel graph nauty sat syntax
val ERR = mk_HOL_ERR "enumg"

(* read graphs *)

val zn = zip_mat o normalize_nauty;

(* -------------------------------------------------------------------------
   Going up and down the latice of graphs
   ------------------------------------------------------------------------- *)

fun all_children mi = 
  let 
    val m = unzip_mat mi 
    val edgel = all_holes m
    val edgecl = List.concat (map (fn x => [(x,blue),(x,red)]) edgel)
    fun mk_child ((i,j),c) = 
      let 
        val _ = mat_update_sym (m,i,j,c)
        val child = zn m
        val _ = mat_update_sym (m,i,j,0)
      in
        child
      end
  in
    map mk_child edgecl
  end

(* -------------------------------------------------------------------------
   Finding the best edge to generalize on
   ------------------------------------------------------------------------- *)

fun score restd mi (i,j) =
  let
    val m = unzip_mat mi 
    val _ = mat_update_sym (m,i,j,0)
    val cl1 = all_children (zn m)
    val cl2 = filter (fn x => emem x restd) cl1
  in
    length cl2
  end

fun best_edge restd mi edgel =
  let val l = map_assoc (score restd mi) edgel in
    fst (hd (dict_sort compare_imax l))
  end
  handle Empty => raise ERR "best_edge" "empty"

(* -------------------------------------------------------------------------
   Generalization step
   ------------------------------------------------------------------------- *)

fun rm_child restd c = restd := erem c (!restd)


fun cover_aux restd acc = case elist (!restd) of [] => rev acc | mi :: _ =>  
  let
    val m = unzip_mat mi
    val edgel = map fst (mat_to_edgecl m)
    val (i,j) = best_edge (!restd) mi edgel
    val _ = mat_update_sym (m,i,j,0)
    val mgi = zn m
    val cl = filter (fn x => emem x (!restd)) (all_children mgi)
  in
    if null cl 
    then cover_aux restd acc
    else (app (rm_child restd) cl; cover_aux restd (mgi :: acc))
  end

fun cover l = 
  let
    val restd = ref (enew IntInf.compare l)
    val (newl,t) = add_time (cover_aux restd) []
    val _ = log ("time: " ^ rts_round 2 t ^ " " ^ its (length newl))
  in
    newl
  end
  
fun iter_cover l =
  let
    val newl = cover l 
  in
    if length newl = length l then raise ERR "iter_cover" "stable" else
    if length newl <= 1000 then newl else iter_cover newl
  end
  
(* -------------------------------------------------------------------------
   Extension step that avoids splitting on holes
   ------------------------------------------------------------------------- *)

fun extend_one mi =
  let
    val mem = !disable_log
    val _ = disable_log := true
    val m = unzip_mat mi
    val _ = skipd_glob := enew Int.compare (map edge_to_var (all_holes m))
    val _ = (iso_flag := false; debug_flag := false; proof_flag := false)
    val ml1 = sat_solver_edgecl (mat_to_edgecl m) (mat_size m + 1) (4,4)
    val ml2 = mk_fast_set IntInf.compare (map zn ml1)
    val _ = disable_log := mem
  in
    ml2
  end;
  
fun extend l = 
  mk_fast_set IntInf.compare (List.concat (map extend_one l));


(* -------------------------------------------------------------------------
   Parallelization of cover
   ------------------------------------------------------------------------- *)

fun find_gen miset mi = 
  let
    val m = unzip_mat mi
    val edgel = map fst (mat_to_edgecl m)
    val (i,j) = best_edge miset mi edgel
    val _ = mat_update_sym (m,i,j,0)
    val mgi = zn m
    val cl = filter (fn x => emem x miset) (all_children mgi)
  in
    mgi :: cl
  end

fun write_infset file set = writel file (map infts (elist set))
fun read_infset file = enew IntInf.compare (map stinf (readl file))

fun write_infl file l = writel file (map infts l)
fun read_infl file = map stinf (readl file)

fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))

val enumgspec : (IntInf.int Redblackset.set, IntInf.int, IntInf.int list)
  smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "enumg.enumgspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = find_gen,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = write_infl,
  read_result = read_infl
  }

fun update_set (set,result) (mi,cl) =
  let val cl' = filter (fn x => (emem x (!set))) cl in
    if null cl' then () else
    (
    result := mi :: !result;
    app (fn c => set := erem c (!set)) cl'
    )
  end

fun cover_para_aux ncore set result = 
  if elength (!set) <= 0 then rev (!result) else
  let
    val n = Int.min (ncore * 100, elength (!set))
    val mil1 = random_subset n (elist (!set))
    val n' = Int.min (n,ncore)
    val mil2 = smlParallel.parmap_queue_extern n' enumgspec (!set) mil1
    val mil3 = map (fn x => (hd x, tl x)) mil2
    val mil4 = map_assoc (length o snd) mil3
    val mil5 = map fst (dict_sort compare_imax mil4)
    val _ = app (update_set (set,result)) mil5
  in
    cover_para_aux ncore set result
  end
  
fun cover_para ncore initset =
  let 
    val result = ref []  
    val set = ref initset
  in
    cover_para_aux ncore set result
  end

(* -------------------------------------------------------------------------
   Gradually increasing the number of edges
   ------------------------------------------------------------------------- *)

fun enumg_loop dir curn startn stopn l =
  if curn >= stopn then () else
  let 
    val _ = log "extension"
    val (lext,t) = if curn = startn then (l,0.0) else add_time extend l
    val _ = log (its (length lext) ^ " extensions in " ^ 
                 rts_round 2 t ^ " seconds")
    val _ = log "iterative cover"
    val (lgen,t) = add_time iter_cover lext
    val _ = log (its (length lgen) ^ " generalizations in " ^ 
                 rts_round 2 t ^ " seconds")
    val _ = write_infl (dir ^ "/gen" ^ its curn) lgen           
  in
    enumg_loop dir (curn+1) startn stopn lgen
  end
  
fun enumg expname (bluen,redn) startn stopn = 
  let 
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = logfile := dir ^ "/log" 
    val _ = app mkDir_err [selfdir ^ "/exp",dir] 
    val l = enum.read_enum startn (bluen,redn)
  in
    enumg_loop dir startn startn stopn l
  end

(*
load "enumg"; load "enum"; 
open aiLib kernel enum enumg;

fun 

val (l8gen,t) = add_time iter_cover l8;
val _ = write_
val l9 = extend l8gen;
val (l9gen,t) = add_time iter_cover l9;
val l10 = extend l9gen;
val (l10gen,t) = add_time iter_cover l10;

fun write_infl file l = writel file (map infts l);
write_infl 

*)


end (* struct *)

