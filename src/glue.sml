(* =========================================================================
   Glue generalized graphs with the help of cone clauses.
   ========================================================================= *)
   
structure glue :> glue =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph sat gen syntax
  minisatProve
val ERR = mk_HOL_ERR "glue"

(* -------------------------------------------------------------------------
   Create clauses from graphs
   ------------------------------------------------------------------------- *)
   
(* this reduction step will need to be reproduced in the proof *)
fun reduce_clause mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 
        then reduce_clause mat (lit :: acc) m
      else if color = newcolor 
        then reduce_clause mat acc m else NONE
    end;

fun satvar i j = mk_var ("E_" ^ its i ^ "_" ^ its j,bool)

fun invsatlit ((i,j),c) = 
   if c = 2 then satvar i j
   else if c = 1 then mk_neg (satvar i j)
   else raise ERR "invsatlit" "unexpected"

fun satclause clause = list_mk_disj (map invsatlit clause)

fun ramsey_clauses_mat (bluen,redn) mat =
  List.mapPartial (reduce_clause mat []) 
    (ramsey_clauses_bare (mat_size mat) (bluen,redn));

fun glue_pb (bluen,redn) m1i m2i =
  let 
    val m = diag_mat (unzip_mat m1i) (unzip_mat m2i)
    val clausel = ramsey_clauses_mat (bluen,redn) m
    val clausetml = map satclause clausel
  in
    mk_neg (list_mk_conj clausetml)
  end
  
fun glue (bluen,redn) m1i m2i = SAT_PROVE (glue_pb (bluen,redn) m1i m2i)

(* -------------------------------------------------------------------------
   Exporting problems in the dimacs format
   ------------------------------------------------------------------------- *)

fun write_dimacs file clausel = 
  let
    val edgel = mk_fast_set edge_compare (map fst (List.concat clausel))
    val mapping = number_snd 1 edgel
    val edged = dnew edge_compare mapping
    fun g ((i,j),c) = 
      if c = 1 then "-" ^ its (dfind (i,j) edged) 
      else if c = 2 then its (dfind (i,j) edged)
      else raise ERR "write_dimacs" "unexpected color"       
    fun f clause = String.concatWith " " (map g clause) ^ " 0"
    val header = "p cnf " ^ its (dlength edged) ^ " " ^ its (length clausel)
    fun h ((i,j),v) = its i ^ "," ^ its j ^ " " ^ its v
  in
    writel file (header :: map f clausel);
    writel (file ^ "_map") (map h mapping)
  end

(* -------------------------------------------------------------------------
   Reading allsat problems
   All edges appear in the satisfiable assignments 
   because there are cliques with only unknown edges 
   ------------------------------------------------------------------------- *)

fun read_map file = 
  let 
    val sl = readl file
    fun f s = 
      let 
        val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) 
        val (s1a,s1b) = pair_of_list (String.tokens (fn x => x = #",") s1) 
      in
        ((string_to_int s1a, string_to_int s1b), string_to_int s2)
      end
  in 
    dnew Int.compare (map (swap o f) sl)
  end;

fun read_sol_one d sl =
  let
    val sl2 = map (fn x => tl (String.tokens Char.isSpace x)) sl
    val il3 = filter (fn x => x <> 0) (map string_to_int (List.concat sl2))
    fun f x = (dfind (Int.abs x) d : int * int, if x > 0 then 1 else 2)
  in
    map f il3
  end

fun read_sol file = 
  let 
    val d = read_map (file ^ "_map")
    val sl0 = readl (file ^ "_sol")
  in
    if last sl0 = "s SOLUTIONS 0" then [] else
    let
      val sl1 = tl (butlast (readl (file ^ "_sol")))
      val sll1 = rpt_split_sl "s SATISFIABLE" sl1    
    in
      map (read_sol_one d) sll1
    end 
  end


(* -------------------------------------------------------------------------
   Sampling from a large cartesian product
   ------------------------------------------------------------------------- *)

fun sample_cartesian_one d c1 c2 =
  let 
    val c1e = random_elem c1
    val c2e = random_elem c2
  in
    if emem (c1e,c2e) d 
    then sample_cartesian_one d c1 c2
    else (c1e,c2e)
  end
  
fun sample_cartesian_loop n d c1 c2 = 
  if elength d >= n then elist d else
  let 
    val (c1e,c2e) = sample_cartesian_one d c1 c2 
    val newd = eadd (c1e,c2e) d  
  in
    sample_cartesian_loop n newd c1 c2
  end
  
fun sample_cartesian n c1 c2 =
  let val d = eempty (cpl_compare IntInf.compare IntInf.compare) in
    sample_cartesian_loop n d c1 c2
  end
    
fun random_cartesian_subset n c1 c2 =
  let
    val n1 = length c1
    val n2 = length c2
  in 
    if n1 * n2 < 100000 
    then random_subset n (cartesian_product c1 c2)
    else sample_cartesian n c1 c2
  end 

(* -------------------------------------------------------------------------
   Benchmarking covers
   ------------------------------------------------------------------------- *)

val extend_flag = ref 2

fun benchmark_one () (c1e,c2e) = 
  let 
    val dir = !smlExecScripts.buildheap_dir
    val picodir = dir ^ "/pico"
    val m1 = diag_mat (unzip_mat c1e) (unzip_mat c2e)
    val m2 = extend_mat m1 (!extend_flag)
    val clausel = ramsey_clauses_mat (4,5) m2
    val file = picodir ^ "/" ^ infts c1e ^ "_" ^ infts c2e
    val fileout = file ^ "_sol"
    val _ = write_dimacs file clausel
    val picobin = selfdir ^ "/../picosat-965/picosat"
    val cmd = picobin ^ " -o " ^ fileout ^ " --all " ^ file
    val (_,t) = add_time (cmd_in_dir picodir) cmd
    val n = length (read_sol file)
  in
    (t,n)
  end

fun write_unit file _ = ()
fun read_unit file = ()
fun write_infinf file (i1,i2) = writel file (map infts [i1,i2])
fun read_infinf file = pair_of_list (map stinf (readl file))
fun write_result file (r,i) = writel file [rts r, its i]
fun read_result file = 
  let val (s1,s2) = pair_of_list (readl file) in
    (valOf (Real.fromString s1), string_to_int s2)
  end

val benchspec : 
  (unit, IntInf.int * IntInf.int, real * int) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "glue.benchspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = benchmark_one,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_infinf,
  read_arg = read_infinf,
  write_result = write_result,
  read_result = read_result
  }

fun benchmark expname n c1 c2 = 
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    val picodir = dir ^ "/pico"
    val _ = app mkDir_err [expdir,dir,picodir]
    val n1 = length c1
    val n2 = length c2
    val pbl = random_cartesian_subset n c1 c2
    val _ = smlExecScripts.buildheap_dir := dir
    val ril = smlParallel.parmap_queue_extern ncore benchspec () pbl
    fun f (r,i) = rts r ^ " " ^ its i
    val rl = map fst ril
    val mean = average_real rl
    val maxt = list_rmax rl
    val expt = (mean * Real.fromInt (n1 * n2)) / (60.0 * 60.0 * 24.0);
  in
    writel (dir ^ "/summary") 
      (map rts [expt,mean,maxt] @
       map its [n,sum_int (map snd ril),n1,n2,n1*n2] @
       map f ril)
  end

(*
load "glue"; open aiLib kernel graph glue;
load "enum"; open enum;
load "genv"; open genv;

val c1 = read_enum 10 (3,5);
val c2 = read_enum 14 (4,4);
benchmark "v0v0" 100 c1 c2;

val c2v2 = compute_cover 2 c2;
benchmark "v0v2e" 100 c1 (map fst c2v2);

*)


(*
load "glue"; open aiLib kernel graph glue;
load "enum"; open enum;

val dir = selfdir ^ "/pico";
clean_dir dir;
val file = dir ^ "/test";

val csize = 10;
val m1 = random_elem (enum.read_enum csize (3,5));
val m2 = random_elem (enum.read_enum (24 - csize) (4,4));
val m2u = unzip_mat m2;
val m2sub = zip_mat (random_subgraph (mat_size m2u - 2) m2u);
writel (file ^ "_mat") (map infts [m1,m2sub]);

val m = diag_mat (unzip_mat m1) (unzip_mat m2sub);
val clausel = ramsey_clauses_mat (4,5) m;
val _ = write_dimacs file clausel;
val cmd = "../../picosat-965/picosat -o " ^ file ^ "_sol --all " ^ file;
val (_,t) = add_time (cmd_in_dir dir) cmd;
val soll = read_sol file;

val m3 = diag_mat (unzip_mat m1) (unzip_mat m2sub);
val sol = hd soll;
val m4 = edgecl_to_mat (mat_size m3) (mat_to_edgecl m3 @ sol);
print_mat m3;
print_mat m4;
is_ramsey (4,5) m4;

(* extension steps *)


val m4' = edgecl_to_mat (mat_size m3 + 2) (mat_to_edgecl m3 @ sol);
print_mat m4';
val clausel = ramsey_clauses_mat (4,5) m4';
val file = dir ^ "/teste";
write_dimacs file clausel;
val cmd = "../../picosat-965/picosat -o " ^ file ^ "_sol --all " ^ file;
val (_,t) = add_time (cmd_in_dir dir) cmd;
val sl = readl (file ^ "_sol");
val soll = read_sol file;

*)



(* -------------------------------------------------------------------------
   Write gluing scripts
   ------------------------------------------------------------------------- *)

fun write_gluescript dirname (b1,r1,size1) (b2,r2,size2) (bluen,redn)    
  (batchi,ipairl) = 
  let 
    val s1 = its b1 ^ its r1 ^ its size1
    val s2 = its b2 ^ its r2 ^ its size2
    val id = s1 ^ "_" ^ s2
    val thyname = "ramseyGlue" ^ id ^ "_" ^ its batchi
    val filename = selfdir ^ "/" ^ dirname ^ "/" ^ thyname ^ "Script.sml"
    val param = "(" ^ its bluen ^ "," ^ its redn ^ ")"
    val open_cmd = ["open HolKernel boolLib kernel glue"]
    val newtheory_cmd = ["val _ = new_theory " ^ mlquote thyname]
    fun save_cmd (i,(m1i,m2i)) = 
      let 
        val thmname = "Glue" ^ id ^ "_" ^ its i 
        val graph1 = "(stinf " ^ mlquote (infts m1i) ^ ")"
        val graph2 = "(stinf " ^ mlquote (infts m2i) ^ ")"
        val argls = String.concatWith " " [param,graph1,graph2]
      in
        "val _ = save_thm (" ^  mlquote thmname ^ ", glue " ^ argls ^ ")"
      end
    val export_cmd = ["val _ = export_theory ()"]
  in
    writel filename (open_cmd @ newtheory_cmd @
       map save_cmd ipairl @ export_cmd)
  end

fun write_gluescripts dirname batchsize
  (b1,r1,size1) (b2,r2,size2) (bluen,redn) = 
  let
    val _ = mkDir_err (selfdir ^ "/" ^ dirname)
    val parl1 = read_par size1 (b1,r1)
    val _ = print_endline ("parl1: " ^ its (length parl1))
    val parl2 = read_par size2 (b2,r2)
    val _ = print_endline ("parl2: " ^ its (length parl2))
    val pairl = cartesian_product parl1 parl2
    val _ = print_endline ("pairl: " ^ its (length pairl))
    fun difficulty (a,b) = 
      number_of_holes (unzip_mat a) + number_of_holes (unzip_mat b)
    val pairlsc = map_assoc difficulty pairl
    val sortedl = map fst (dict_sort compare_imax pairlsc)
    val ncut = (length sortedl div batchsize) + 1
    val batchl = number_fst 0 (cut_modulo ncut (number_fst 0 sortedl))
  in
    app (write_gluescript dirname (b1,r1,size1) (b2,r2,size2) (bluen,redn))
    batchl
  end

end (* struct *)

(*
load "glue"; open kernel glue;
fun f i = if i = 11 then () else 
  write_gluescripts "glue" 1 (3,5,i) (4,4,24-i) (4,5);
val _ = range (7,13,f);
*)

(*
load "glue"; open kernel glue;
fun f i = if i = 10 orelse i = 11 orelse i = 12 then () else 
  write_gluescripts "glue" 1 (3,5,i) (4,4,24-i) (4,5);
val _ = range (7,13,f);
*)


