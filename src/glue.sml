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
    (ramsey_clauses_bare (mat_size mat) (bluen,redn));


fun satvar i j = mk_var ("E_" ^ its i ^ "_" ^ its j,bool)

fun invsatlit ((i,j),c) = 
   if c = 2 then satvar i j
   else if c = 1 then mk_neg (satvar i j)
   else raise ERR "invsatlit" "unexpected"

fun satclause clause = list_mk_disj (map invsatlit clause)



fun satpb_of_clausel clausel =
  let val clausetml = map satclause clausel in
    mk_neg (list_mk_conj clausetml)
  end
  
fun glue_pb (bluen,redn) m1i m2i =
  let 
    val m = diag_mat (unzip_mat m1i) (unzip_mat m2i)
    val clausel = ramsey_clauses_mat (bluen,redn) m
  in
    satpb_of_clausel clausel
  end
  
fun glue (bluen,redn) m1i m2i = SAT_PROVE (glue_pb (bluen,redn) m1i m2i)

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

fun benchmark_one () (c1e,c2e) = 
  let 
    val m1 = diag_mat (unzip_mat c1e) (unzip_mat c2e)
    val clausel = ramsey_clauses_mat (4,5) m1
    val (_,t) = add_time SAT_PROVE (satpb_of_clausel clausel)
  in
    t
  end

fun write_unit file _ = ()
fun read_unit file = ()
fun write_infinf file (i1,i2) = writel file (map infts [i1,i2])
fun read_infinf file = pair_of_list (map stinf (readl file))
fun write_result file r = writel file [rts r]
fun read_result file = (valOf o Real.fromString o hd o readl) file

val benchspec : (unit, IntInf.int * IntInf.int, real) smlParallel.extspec =
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
    val _ = app mkDir_err [expdir,dir]
    val n1 = length c1
    val n2 = length c2
    val pbl = random_cartesian_subset n c1 c2
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val rl = smlParallel.parmap_queue_extern ncore benchspec () pbl
    fun f ((c1e,c2e),r) = infts c1e ^ "," ^ infts c2e ^ " " ^ rts r
    val mean = average_real rl
    val maxt = list_rmax rl
    val expt = (mean * Real.fromInt (n1 * n2)) / (60.0 * 60.0 * 24.0);
    val heads = String.concatWith " " 
      (map rts [expt,mean,maxt] @ map its [n,n1,n2,n1*n2])
  in
    writel (dir ^ "/summary") [heads];
    writel (dir ^ "/sattime") (map f (combine (pbl,rl)))
  end
  
fun benchmark_pbl expname pbl = 
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    val _ = app mkDir_err [expdir,dir]
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val rl = smlParallel.parmap_queue_extern ncore benchspec () pbl
    fun f ((c1e,c2e),r) = infts c1e ^ "," ^ infts c2e ^ " " ^ rts r
    val mean = average_real rl
    val maxt = list_rmax rl
    val heads = String.concatWith " " (map rts [mean,maxt])
  in
    writel (dir ^ "/summary") [heads];
    writel (dir ^ "/sattime") (map f (combine (pbl,rl)))
  end
  
fun tune prefix nex (case35,hole35,hole44,expo)  = 
  let 
    val case44 = 24 - case35
    fun msg s = append_endline (selfdir ^ "/log_bench_info") s
    fun msg2 s = append_endline (selfdir ^ "/log_bench") s
    val (a,b) = split_string "." (rts_round 3 expo)
    val exps = a ^ "_" ^ b
    val expname = prefix ^ "_" ^ its case35 ^ "_" ^ 
      its hole35 ^ "_" ^ its hole44 ^ "_" ^ exps
    val _ = msg expname
    val _ = clean_dir (selfdir ^ "/gen")
    val _ = exponent := expo
    val _ = maxhole := hole35
    val _ = select_number1 := 313
    val _ = select_number2 := 1
    val (_,t) = add_time (gen (3,5)) (case35,case35)
    val _ = msg ("35: " ^ rts_round 2 t) 
    val _ = maxhole := hole44
    val _ = select_number1 := 1000
    val _ = select_number2 := 100
    val (_,t) = add_time (gen (4,4)) (case44,case44)
    val _ = msg ("44: " ^ rts_round 2 t) 
    val _ = cmd_in_dir selfdir ("cp -r gen gen_" ^ expname)
    val set1 = read_par case35 (3,5)
    val set2 = read_par case44 (4,4)
    val (_,t) = add_time (benchmark expname nex set1) set2
    val _ = msg ("glue: " ^ rts_round 2 t) 
    val s = hd (readl (selfdir ^ "/exp/" ^ expname ^ "/summary"))
  in
    msg2 (expname ^ " " ^ s)
  end
  
fun tune_3512 prefix nex (hole35,hole44,expo)  = 
  let 
    val case35 = 12
    val case44 = 24 - case35
    fun msg s = append_endline (selfdir ^ "/log_bench_info") s
    fun msg2 s = append_endline (selfdir ^ "/log_bench") s
    val (a,b) = split_string "." (rts_round 3 expo)
    val exps = a ^ "_" ^ b
    val expname = prefix ^ "_" ^ its case35 ^ "_" ^ 
      its hole35 ^ "_" ^ its hole44 ^ "_" ^ exps
    val _ = msg expname
    val _ = clean_dir (selfdir ^ "/gen")
    val _ = exponent := expo
    val _ = maxhole := hole35
    val _ = select_number1 := 313
    val _ = select_number2 := 1
    val (_,t) = add_time (gen (3,5)) (case35,case35)
    val _ = msg ("35: " ^ rts_round 2 t) 
    val _ = 
      if hole44 = 8 
        then cmd_in_dir selfdir "cp gen_e88/gen4412 gen/gen4412"
      else if hole44 = 6
        then cmd_in_dir selfdir 
          "cp gen_bench11_12_6_6_0_5_1000_100/gen4412 gen/gen4412"
      else raise ERR "tune_3512" ""
    val _ = cmd_in_dir selfdir ("cp -r gen gen_" ^ expname)
    val set1 = read_par case35 (3,5)
    val set2 = read_par case44 (4,4)
    val (_,t) = add_time (benchmark expname nex set1) set2
    val _ = msg ("glue: " ^ rts_round 2 t) 
    val s = hd (readl (selfdir ^ "/exp/" ^ expname ^ "/summary"))
  in
    msg2 (expname ^ " " ^ s)
  end
  
fun tune_3510 prefix nex (hole35,expo)  = 
  let 
    val case35 = 10
    val case44 = 24 - case35
    fun msg s = append_endline (selfdir ^ "/log_bench_info") s
    fun msg2 s = append_endline (selfdir ^ "/log_bench") s
    val (a,b) = split_string "." (rts_round 3 expo)
    val exps = a ^ "_" ^ b
    val expname = prefix ^ "_" ^ its case35 ^ "_" ^ its hole35 ^ "_0_" ^ exps
    val _ = msg expname
    val _ = clean_dir (selfdir ^ "/gen")
    val _ = exponent := expo
    val _ = maxhole := hole35
    val _ = select_number1 := 313
    val _ = select_number2 := 1
    val (_,t) = add_time (gen (3,5)) (case35,case35)
    val _ = msg ("35: " ^ rts_round 2 t)
    val _ = cmd_in_dir selfdir ("cp -r gen gen_" ^ expname)
    val set1 = read_par case35 (3,5)
    val set2 = enum.read_enum case44 (4,4)
    val (_,t) = add_time (benchmark expname nex set1) set2
    val _ = msg ("glue: " ^ rts_round 2 t) 
    val s = hd (readl (selfdir ^ "/exp/" ^ expname ^ "/summary"))
  in
    msg2 (expname ^ " " ^ s)
  end



fun benchmark_pbl expname pbl = 
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    val _ = app mkDir_err [expdir,dir]
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val rl = smlParallel.parmap_queue_extern ncore benchspec () pbl
    fun f ((c1e,c2e),r) = infts c1e ^ "," ^ infts c2e ^ " " ^ rts r
    val mean = average_real rl
    val maxt = list_rmax rl
    val heads = String.concatWith " " (map rts [mean,maxt])
  in
    writel (dir ^ "/summary") [heads];
    writel (dir ^ "/sattime") (map f (combine (pbl,rl)))
  end

(* -------------------------------------------------------------------------
   Glueing generalizations
   ------------------------------------------------------------------------- *)

fun glue_one () (c1e,c2e) = 
  let 
    val m1 = diag_mat (unzip_mat c1e) (unzip_mat c2e)
    val clausel = ramsey_clauses_mat (4,5) m1
    val name = "r45_" ^ infts c1e ^ "_" ^ infts c2e 
    val _ = new_theory name
    val (thm,t) = add_time SAT_PROVE (satpb_of_clausel clausel)
    val _ = print_endline ("time: " ^ rts t)
    val _ = save_thm (name,thm)
    val olddir = OS.FileSys.getDir ()
    val newdir = !smlExecScripts.buildheap_dir ^ "/theories"
    val _ = OS.FileSys.chDir newdir
    val _ = export_theory ()
    val _ = OS.FileSys.chDir olddir
  in
    t
  end

fun write_unit file _ = ()
fun read_unit file = ()
fun write_infinf file (i1,i2) = writel file (map infts [i1,i2])
fun read_infinf file = pair_of_list (map stinf (readl file))
fun write_result file r = writel file [rts r]
fun read_result file = (valOf o Real.fromString o hd o readl) file

val gluespec : (unit, IntInf.int * IntInf.int, real) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "glue.gluespec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = glue_one,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_infinf,
  read_arg = read_infinf,
  write_result = write_result,
  read_result = read_result
  }

fun order_pbl ml1 ml2 = 
  let 
    val pbl1 = cartesian_product ml1 ml2
    val pbl2 = map_assoc difficulty_pair pbl1
  in
    map fst (dict_sort compare_rmin pbl2)
  end
  
fun glue_pbl expname pbl = 
  let
    val expdir = selfdir ^ "/exp"
    val dir = expdir ^ "/" ^ expname
    val _ = app mkDir_err [expdir,dir,dir ^ "/theories"]
    val _ = smlExecScripts.buildheap_dir := dir
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val rl = smlParallel.parmap_queue_extern ncore gluespec () pbl
    fun f ((c1e,c2e),r) = infts c1e ^ "," ^ infts c2e ^ " " ^ rts r
    val mean = average_real rl
    val maxt = list_rmax rl
    val heads = String.concatWith " " (map rts [mean,maxt])
  in
    writel (dir ^ "/summary") [heads];
    writel (dir ^ "/sattime") (map f (combine (pbl,rl)))
  end

(* -------------------------------------------------------------------------
   Glueing
   ------------------------------------------------------------------------- *)

(*
export TMPDIR="$PWD/tmp";
mkdir tmp;
find /tmp -maxdepth 1 -type f -name 'MLTEMP*' ! -exec rm {} \;

load "glue"; open aiLib kernel graph enum gen glue;

val ml1 = read_par 10 (3,5);
val ml2 = read_par 14 (4,4);
val pbl = order_pbl ml1 ml2;

glue_pbl "glue3510" pbl;

noclique 24 (4,true);   
noclique 24 (5,false);


*)

(* -------------------------------------------------------------------------
   Running on one example
   ------------------------------------------------------------------------- *)

(*
load "glue"; open aiLib kernel graph glue;
load "enum"; open enum;
load "gen"; open gen;
val c1 = hd (read_par 10 (3,5));
val c2 = hd (read_par 14 (4,4));
val (_,t2) = add_time (glue (4,5) c1) c2;
*)

(* -------------------------------------------------------------------------
   Benchmarking
   ------------------------------------------------------------------------- *)

(*
export TMPDIR="$PWD/tmp";
mkdir tmp;
find /tmp -maxdepth 1 -type f -name 'MLTEMP*' ! -exec rm {} \;

load "glue"; open aiLib kernel graph enum gen glue;

val parameterl1 = 
  [(4,4,0.5),(4,4,2.0)] @
  [(4,4,1.0),(3,4,1.0),(4,3,1.0),(5,4,1.0),(4,5,1.0)];
 
app (tune "bench") parameterl1; 
 
val parameterl2 = [(4,4,1.0),(4,4,0.1),(4,4,10.0)];          
app (tune "bench2") parameterl2;

(* default *)
val parameterl3 = [(4,4,0.0)];          
app (tune "bench3") parameterl3;

(* difficulty only *)
val parameterl4 = [(4,4,1.0)];          
app (tune "bench4") parameterl4;

(* variable then difficulty *)
val parameterl5 = [(4,4,1.0)];          
app (tune "bench5") parameterl5;


val parameterl6 = [(4,4,0.01),(4,4,0.1),(4,4,0.5)];
app (tune "bench6") parameterl6;

val parameterl7 = [(8,8,0.5),(9,9,0.5),(10,10,0.5)];  
app (tune "bench7") parameterl7;

val parameterl8 = [(10,5,5,0.5)]

val parameterl9 = [(12,8,8,0.5,1000,100)];

val parameterl11 = [(12,6,6,0.5,1000,100)];
app (tune "bench11") parameterl11;

val parameterl12 = [(0,8,0.5),(2,6,0.5),(1,8,0.5),(3,6,0.5),(2,8,0.5),(3,8,0.5)];
app (tune_3512 "bench12") parameterl12;

val parameterl14 = [(10,2,5,0.5),(10,3,5,0.5),(10,2,6,0.5)];
app (tune "bench14" 100) parameterl14;

val parameterl15 = [(10,2,5,0.5),(10,3,5,0.5),(10,2,6,0.5)];
app (tune_3510 "bench15" 100) parameterl14;
*)

(* -------------------------------------------------------------------------
   Analysis of the relation between size/number of clauses and speed
   ------------------------------------------------------------------------- *)

(*
load "glue"; open aiLib kernel graph glue;
load "enum"; open enum;
load "gen"; open gen;
val expname = "e0e0bis";
val sl1 = readl (selfdir ^ "/exp/" ^ expname ^ "/summary");
val sl2 = readl (selfdir ^ "/exp/" ^ expname ^ "/sattime");

fun read_sattime expname =
  let
    val filename = selfdir ^ "/exp/" ^ expname ^ "/sattime"
    fun f s =
      let 
        val (sa,sb) = pair_of_list (String.tokens Char.isSpace s)
        val (sa1,sa2) = pair_of_list (String.tokens (fn x => x = #",") sa)
      in
        ((stinf sa1, stinf sa2), valOf (Real.fromString sb))
      end
   in
     map f (readl filename)
   end;

val clausel4524 = sat.ramsey_clauses_bare 24 (4,5);

fun reduce_clause mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 
        then reduce_clause mat (lit :: acc) m
      else if color = newcolor 
        then reduce_clause mat acc m else NONE
    end;

fun score (a,b) = 
  let 
    val m = diag_mat (unzip_mat a) (unzip_mat b)
    val clausel = List.mapPartial (reduce_clause m []) clausel4524;
    val lenl = map length clausel;
    val l = dlist (count_dict (dempty Int.compare) lenl)
    fun sc_one (a,b) = int_div b (int_pow 2 a)
  in
    sum_real (map sc_one l)
  end;

fun mk_data expname = 
  let
    val l1 = read_sattime expname
    val l2 = map_fst score l1
    val l3 = dict_sort (fst_compare Real.compare) l2
  in
    app print_endline (map (rts o fst) l3);
    print_endline "###";
    app print_endline (map (rts o snd) l3)
  end;
    
mk_data "e0e0bis";
*)

end (* struct *)




