(* =========================================================================
   Enumerate R(a,b,k) graphs (in particular R(3,5,k) and R(4,4,k))
   ========================================================================= *)
   
structure enum :> enum =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty sat
val ERR = mk_HOL_ERR "enum"

fun add_vertex (bluen,redn) set graphi =
  let
    val graph = unzip_mat graphi
    val size = mat_size graph + 1
    val _ = (iso_flag := false;  proof_flag := false)
    val graphl = sat_solver_edgecl (mat_to_edgecl graph) size (bluen,redn)
    val il = map (zip_mat o nauty.normalize_nauty) graphl
  in
    set := eaddl il (!set)
  end

fun enum_worker br (i,il) = 
  let  
    val set = ref (eempty IntInf.compare) 
    val dir = !smlExecScripts.buildheap_dir ^ "/graphs"
    val file = dir ^ "/" ^ its i
  in
    app (add_vertex br set) il;
    (writel file (map IntInf.toString (elist (!set)))
     handle SysErr _ => raise ERR "enum_worker" file)
  end

fun merge_one set file = 
  set := eaddl (map stinf (readl file)) (!set)

fun merge_graphs dir = 
  let 
    val set = ref (eempty IntInf.compare) 
    val filel = map (fn x => dir ^ "/" ^ x) (listDir dir)
  in
    app (merge_one set) filel; !set
  end  

fun write_iil file (i,il) = writel file (its i :: map infts il)

fun read_iil file =
  let val sl = readl file in
    (string_to_int (hd sl), map stinf (tl sl))
  end

fun write_br file (bluen,redn) = writel file [its bluen, its redn]
fun read_br file = pair_of_list (map string_to_int (readl file))

val enumspec : (int * int, int * IntInf.int list, unit) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "enum.enumspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = enum_worker,
  write_param = write_br,
  read_param = read_br,
  write_arg = write_iil,
  read_arg = read_iil,
  write_result = let fun f _ () = () in f end,
  read_result = let fun f _ = () in f end
  }

fun parallel_extend ncore expname br set =
  let  
    val dir = selfdir ^ "/exp/" ^ expname
    val _ = mkDir_err (selfdir ^ "/exp")
    val _ = clean_dir dir
    val _ = clean_dir (dir ^ "/graphs")
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory 
    val _ = smlExecScripts.buildheap_dir := dir
    val batchl = number_fst 0 (cut_n (3 * ncore) (elist set))
    val _ = clean_dir (selfdir ^ "/parallel_search")
    val _ = smlParallel.parmap_queue_extern ncore enumspec br batchl
  in
    merge_graphs (dir ^ "/graphs")
  end
    
fun serial_extend br set = 
  let val newset = ref (eempty IntInf.compare) in
    Redblackset.app (add_vertex br newset) set; !newset
  end

fun write_enum size (bluen,redn) il =
  let 
    val dir = selfdir ^ "/enum"
    val enumname = "enum" ^ its bluen ^ its redn ^ its size
    val sl = map infts il
  in
    mkDir_err dir;
    writel (dir ^ "/" ^ enumname) sl;
    log ("stored: " ^ enumname)
  end
  
fun read_enum size (bluen,redn) =
  let 
    val dir = selfdir ^ "/enum"
    val enumname = "enum" ^ its bluen ^ its redn ^ its size
  in
    map stinf (readl (dir ^ "/" ^ enumname))
  end
  
fun extend_loop size (br as (bluen,redn)) set = 
  let
    val expname = "R" ^ its bluen ^ its redn ^ its size
    val newset = 
      let val n = Int.min (ncore,elength set) in
        if n <= 1
        then (log "serial extension"; serial_extend br set)
        else (log ("parallel extension: " ^ its n); 
              parallel_extend n expname br set)
      end
    val _ = write_enum size br (elist newset)
  in
    if elength newset <= 0 then () else 
    extend_loop (size+1) (bluen,redn) newset
  end;
  
fun enum (bluen,redn) = 
  let val set = enew IntInf.compare [zip_mat (Array2.array (1,1,0))] in
    extend_loop 2 (bluen,redn) set
  end
    
end (* struct *)

(*
load "enum"; open sat aiLib graph enum;
disable_log := true;
enum (4,4);
enum (3,5);
*)
