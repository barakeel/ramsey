(* =========================================================================
   Compute a set of generalized cones covering a set of cones
   ========================================================================= *)
   
structure cone :> cone =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty sat syntax gen
val ERR = mk_HOL_ERR "cone"
type vleafs = int * int * (IntInf.int * int list) list  

(* -------------------------------------------------------------------------
   Cone generalization
   ------------------------------------------------------------------------- *)

val cone_compare = list_compare Int.compare
val cone_set = mk_fast_set cone_compare   

fun parents cl = case cl of 
    [] => []
  | a :: m => 
    if a <> 0 
    then (0 :: m) :: map (fn x => a :: x) (parents m)
    else map (fn x => a :: x) (parents m)
  
fun instances cl = 
  let val cl' =  map (fn x => if x = 0 then [1,2] else [x]) cl in 
    cartesian_productl cl'
  end
  
fun cnext uset childl = 
  let  
    val childset = enew (list_compare Int.compare) childl
    val l1 = cone_set (List.concat (map parents childl))
    fun is_fullanc m = all (fn x => emem x uset) (instances m)
    val l2 = filter is_fullanc l1
  in
    l2
  end

fun cloop uset childl =
  let val parentl = cnext uset childl in
    if null parentl
    then random_elem childl
    else cloop uset parentl
  end;
  
fun cgeneralize uset leaf = cloop uset [leaf];
  
fun n_hole cl = length (filter (fn x => x = 0) cl);  
  
val attempts_glob = ref 100
  
fun ccover_loop uset = 
  if elength uset <= 0 then [] else 
  let 
    val (parentl1,t) = add_time 
      (map (cgeneralize uset)) (random_subset (!attempts_glob) (elist uset))
    fun uncovered_instances parent = 
      (parent, filter (fn x => emem x uset) (instances parent))
    val parentl2 = map uncovered_instances parentl1
    val parentl3 = map_assoc (length o snd) parentl2
    val ((parent,leafs),sc) = hd (dict_sort compare_imax parentl3)
    val newuset = ereml leafs uset
    (* val _ = log (its (elength newuset) ^ " " ^ rts_round 2 t) *)
  in
    (parent,leafs) :: ccover_loop newuset
  end

fun string_of_cone cone = String.concatWith "_" (map its cone)
fun cone_of_string s = map string_to_int (String.tokens (fn x => x = #"_") s)

fun write_cone (bluen,redn) mati conel =
  let
    val dir = selfdir ^ "/cone"
    val size = mat_size (unzip_mat mati)
    val file = dir ^ "/" ^ its bluen ^ its redn ^ its size ^ "_" ^ infts mati
    val _ = mkDir_err dir
    fun f (cone,conel) = 
      String.concatWith " " (map string_of_cone (cone :: conel)) 
  in
    writel file (map f conel)
  end
  
fun read_cone (bluen,redn) mati = 
  let
    val dir = selfdir ^ "/cone"
    val size = mat_size (unzip_mat mati)
    val file = dir ^ "/" ^ its bluen ^ its redn ^ its size ^ "_" ^ infts mati
    fun f s = 
      let val l = map cone_of_string (String.tokens Char.isSpace s) in
        (hd l, tl l)
      end
  in
    map f (readl file)
  end
  
fun gen_cone (bluen,redn) mati = 
  let
    val mat = unzip_mat mati
    val size = mat_size mat
    val _ = (iso_flag := false; proof_flag := false; conegen_flag := true)    
    val _ = sat_solver_edgecl (mat_to_edgecl mat) (size+1) (bluen,redn)
    val _ = conegen_flag := false
    val coneset = !coneset_glob
    val _ = log ("cones: " ^ its (elength coneset))
    val conel3 = ccover_loop coneset
    val _ = log ("cone generalizations: " ^ its (length conel3))
  in
    write_cone (bluen,redn) mati conel3
  end


fun write_infset file (a,b) = writel file [its a,its b]
fun read_infset file = case readl file of
    [sa,sb] => (string_to_int sa, string_to_int sb)
  | _ => raise ERR "read_infset" ""
 
fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))


val conespec : (int * int, IntInf.int, unit) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "cone.conespec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = gen_cone,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = let fun f file _ = () in f end,
  read_result = let fun f file = () in f end
  }

fun cones45 size (bluen,redn) =
  let 
    val s = its bluen ^ its redn ^ its size
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/cone" ^ s
    val _ = app mkDir_err [expdir,dir]
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options := "--maxheap " ^ its memory
    val par = read_par size (bluen,redn)
    val parn = length par
    val _ = log ("par : " ^ its parn)
    val n' = Int.min (parn,ncore)
    val (_,t) = add_time 
      (smlParallel.parmap_queue_extern n' conespec (4,5)) par
  in
    log ("cones: " ^ rts_round 4 t)
  end

(* -------------------------------------------------------------------------
   Cone proof
   ------------------------------------------------------------------------- *)

fun create_parconethmd (bluen,redn) mi = 
  let 
    val parl = map fst (read_cone (bluen,redn) mi) 
    val size = mat_size (unzip_mat mi)
    val col = List.tabulate (size,fn i => (i,size))
  in
    if null parl then dempty cone_compare else
    let
      fun f parcone =
        let
          val colc = combine (col,parcone)
          val term = term_of_edgecl (size + 1) colc
        in
          UNDISCH_ALL (SPEC_ALL (ASSUME term))
        end
    in
      dnew cone_compare (map_assoc f parl)
    end
  end;

fun CONE45_ONE mati =
  let
    val mat = unzip_mat mati
    val size = mat_size mat
    val cone = read_cone (4,5) mati
    val parconethmd = create_parconethmd (4,5) mati
    val _ = init_conethmd parconethmd cone
    val _ = (debug_flag := false; disable_log := false;
             conep_flag := true; iso_flag := false; proof_flag := true)
    val matl = sat_solver_edgecl (mat_to_edgecl mat) (size+1) (4,5)
    val _ = conep_flag := false
  in
    !final_thm
  end

fun write_conescript size (bluen,redn) (batchi,igraphl) = 
  let 
    val id = its bluen ^ its redn ^ its size
    val batchs = id ^ "_" ^ its batchi
    val thyname = "ramseyCone" ^ batchs
    val filename = selfdir ^ "/conep/" ^ thyname ^ "Script.sml"
    val open_cmd = ["open HolKernel boolLib kernel cone ramseyDefTheory"]
    val newtheory_cmd = ["val _ = new_theory " ^ mlquote thyname]
    fun save_cmd (i,graph) = 
      let 
        val thmname = "Cone" ^ id ^ "_" ^ its i 
        val graphs =  "(stinf " ^ mlquote (infts graph) ^ ")"
      in
        "val _ = save_thm (" ^  mlquote thmname ^ 
        ", CONE45_ONE " ^ graphs ^ ")"
      end
    val export_cmd = ["val _ = export_theory ()"]
  in
    writel filename (open_cmd @ newtheory_cmd @ 
                     map save_cmd igraphl @ export_cmd)
  end

fun write_conescripts batchsize size (bluen,redn) = 
  let
    val _ = mkDir_err (selfdir ^ "/conep")
    val parl = read_par size (bluen,redn)
    val ncut = (length parl div batchsize) + 1
    val _ = print_endline ("par: " ^ its (length parl))
    val l = number_fst 0 (cut_modulo ncut (number_fst 0 parl))
  in
    app (write_conescript size (bluen,redn)) l
  end


(* -------------------------------------------------------------------------
   Generates cones without proof
   ------------------------------------------------------------------------- *)

(*
load "gen"; load "sat"; load "cone";
open aiLib kernel graph sat nauty gen cone;

fun f i = if i = 13 then () else cones45 i (4,4));
val _ = range (11,17,f);
*)

(* -------------------------------------------------------------------------
   Create proof scripts
   ------------------------------------------------------------------------- *)

(*
load "cone"; open kernel cone;
fun f i = if i = 13 then () else write_conescripts 100 i (4,4);
val _ = range (11,17,f);
*)

(* -------------------------------------------------------------------------
   Run proof scripts
   ------------------------------------------------------------------------- *)
   
(*
cd conep
cp ../enumi/Holmakefile Holmakefile
../../HOL/bin/Holmake --no_prereqs -j 40 | tee ../aaa_log_conep
cd ..
*)

(* -------------------------------------------------------------------------
   Check the theorems
   ------------------------------------------------------------------------- *)
   


end (* struct *)






