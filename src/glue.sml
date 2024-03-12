(* =========================================================================
   Glue generalized graphs with the help of cone clauses.
   ========================================================================= *)
   
structure glue :> glue =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph sat gen syntax gluepost
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
   Gluing scripts with custom loader allowing us to limit the memory
   ------------------------------------------------------------------------- *)

fun glue_pair (m1,m2) =
  let 
    val diag = diag_mat (unzip_mat m1) (unzip_mat m2)
    val clausel = ramsey_clauses_mat (4,5) diag
  in
    post (SAT_PROVE (satpb_of_clausel clausel))
  end

fun write_script file (m1,m2) =
  let
    val (m1s,m2s) = (infts m1, infts m2)
    val name = "r45_" ^ m1s ^ "_" ^ m2s
    val sl = 
     ["open HolKernel kernel glue",
      "val _ = new_theory " ^ mlquote name,
      "val _ = save_thm (" ^ mlquote name ^ 
          ", glue_pair (stinf " ^ mlquote m1s ^ ", stinf " ^ mlquote m2s ^ "))",
      "val _ = export_theory ()"]
  in 
    writel file sl
  end
  
fun run_script_one dir (m1,m2) = 
  let 
    val (m1s,m2s) = (infts m1, infts m2)
    val file = dir ^ "/r45_" ^ m1s ^ "_" ^ m2s ^ "_script.sml" 
  in
    write_script file (m1,m2);
    smlExecScripts.exec_script file  
  end
  
fun run_script_pbl dir pbl =
  let 
    val _ = smlExecScripts.buildheap_dir := dir ^ "/buildheap"
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val _ = app mkDir_err [dir,!smlExecScripts.buildheap_dir]
    val _  = writel (dir ^ "/Holmakefile") ["INCLUDES = .."]
  in
    smlParallel.parapp_queue ncore (run_script_one dir) pbl
  end
  
(* -------------------------------------------------------------------------
   Gluing scripts
   ------------------------------------------------------------------------- *)
   
fun write_gluescript_batch dir (batchn,mml) =
  let
    val degree = mat_size (unzip_mat (fst (hd mml)))
    val thyname = "r45_degree" ^ its degree ^ "_batch" ^ its batchn
    val file = dir ^ "/" ^ thyname ^ "Script.sml"
    fun f (m1,m2) = 
      let 
        val (m1s,m2s) = (infts m1, infts m2) 
        val thmname = "r45_" ^ m1s ^ "_" ^ m2s
      in
        "val _ = save_thm (" ^ mlquote thmname ^ 
        ", glue_pair (stinf " ^ mlquote m1s ^ ", stinf " ^ mlquote m2s ^ "))"
      end
    val sl = 
     ["open HolKernel kernel glue",
      "val _ = new_theory " ^ mlquote thyname] @
      map f mml @
     ["val _ = export_theory ()"]
  in 
    writel file sl
  end
   
fun write_gluescript_batchl dir batchpbl = 
  let 
    val _ = mkDir_err dir
    val _ = writel (dir ^ "/Holmakefile") ["INCLUDES = .."]
  in
    app (write_gluescript_batch dir) batchpbl
  end   
 
fun find_scriptl dir =
  map (fn x => dir ^ "/" ^ x) 
    (filter (String.isSuffix "Script.sml") (listDir dir))

fun run_scriptl dir scriptl =
  let 
    val _ = smlExecScripts.buildheap_dir := dir ^ "/buildheap"
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val _ = app mkDir_err [dir,!smlExecScripts.buildheap_dir]
    val ncore' = Int.min (ncore, length scriptl)
  in
    smlParallel.parapp_queue ncore' smlExecScripts.exec_script scriptl
  end

(* -------------------------------------------------------------------------
   Writing problems and batches
   ------------------------------------------------------------------------- *)

fun write_pbl file pbl =
  let fun f (i1,i2) = infts i1 ^ " " ^ infts i2 in
    writel file (map f pbl)
  end
  
fun read_pbl file = 
  let fun f s = 
    let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
      (stinf s1, stinf s2)
    end
  in
    map f (readl file)
  end

fun write_pbbatchl file pbbatchl = 
  let 
    fun f1 (i1,i2) = infts i1 ^ "," ^ infts i2
    fun f2 (batchn,pbl) = 
      its batchn ^ " " ^ (String.concatWith " " (map f1 pbl))
  in
    writel file (map f2 pbbatchl)
  end

fun read_pbbatchl file = 
  let 
    fun f1 s = 
      let val (a,b) = pair_of_list (String.tokens (fn x => x = #",") s) in
        (stinf a, stinf b)
      end
    fun f2 line = 
      let val l = String.tokens Char.isSpace line in
        (string_to_int (hd l), map f1 (tl l))
      end
  in
    map f2 (readl file)
  end  

(* -------------------------------------------------------------------------
   3,5,8 glueing: using gen_bench16_8_4_0_0_5
   ------------------------------------------------------------------------- *)

(*
load "glue"; open aiLib kernel graph enum gen glue;
val ml1 = read_par 8 (3,5);
val ml2 = read_par 16 (4,4);
val pbl = shuffle (cartesian_product ml1 ml2);
write_pbl "glue358_pbl_dai07" pbl;
*)

(* batch 
load "glue"; open aiLib kernel graph enum gen glue;
val pbl = read_pbl (selfdir ^ "/glue358_pbl_dai07");
val batchl = number_fst 0 (mk_batch_full 10 pbl);
write_pbbatchl "glue358_batchl_dai07" batchl;
*)

(* using custom builder
export TMPDIR="$PWD/tmp";
mkdir tmp;
load "glue"; open aiLib kernel graph enum gen glue;
val glue358_pbl_dai07 = map g (readl (selfdir ^ "/glue358_pbl_dai07"));
run_script_pbl (selfdir ^ "/glue358_dai07") glue358_pbl_dai07;
*)

(* using Holmake
load "glue"; open aiLib kernel graph enum gen glue;
val batchl = read_pbbatchl "glue358_batchl_dai07";
write_gluescript_batchl (selfdir ^ "/glue358_dai07_holmake") batchl;

export TMPDIR="$PWD/tmp";
mkdir tmp;
cd glue358_dai07_holmake
../../HOL/bin/Holmake --no_prereqs -j 6 | tee ../aaa_log_glue358
*)

(* -------------------------------------------------------------------------
   3,5,10 glueing: using gen_bench6_4_4_0_5
   ------------------------------------------------------------------------- *)

(*
export TMPDIR="$PWD/tmp";
mkdir tmp;

load "glue"; open aiLib kernel graph enum gen glue;
val ml1 = read_par 10 (3,5);
val ml2 = read_par 14 (4,4);
val pbl = shuffle (cartesian_product ml1 ml2);
val (pbl1,pbl2) = part_n (length pbl div 2) pbl;
write_pbl "glue3510_pbl_dai05" pbl1;
write_pbl "glue3510_pbl_dai06" pbl2;

load "glue"; open aiLib kernel graph enum gen glue;
fun g s = 
  let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
    (stinf s1, stinf s2)
  end;
val pbl_dai05 = map g (readl (selfdir ^ "/glue3510_pbl_dai05"));
run_script_pbl (selfdir ^ "/glue3510_dai05") pbl_dai05;

load "glue"; open aiLib kernel graph enum gen glue;
fun g s = 
  let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
    (stinf s1, stinf s2)
  end;
val pbl_dai06 = map g (readl (selfdir ^ "/glue3510_pbl_dai06"));
run_script_pbl (selfdir ^ "/glue3510_dai06") pbl_dai06;

*)

(* -------------------------------------------------------------------------
   3,5,12 Glueing: using gen_bench12_12_0_8_0_5
   ------------------------------------------------------------------------- *)

(*
load "glue"; open aiLib kernel graph enum gen glue;
val ml1 = read_par 12 (3,5);
val ml2 = read_par 12 (4,4);
val pbl = shuffle (cartesian_product ml1 ml2);
val (pbl1,pbl2) = part_n (length pbl div 2) pbl;
write_pbl "glue3512_pbl_dai04" pbl1;
write_pbl "glue3512_pbl_dai07" pbl2;
*)

(* batch dai04
load "glue"; open aiLib kernel graph enum gen glue;
val pbl = read_pbl (selfdir ^ "/glue3512_pbl_dai04");
val batchl = number_fst 0 (mk_batch_full 200 pbl);
length batchl; (* 806 *)
write_pbbatchl "glue3512_batchl_dai04" batchl;
*)

(* write script dai04
load "glue"; open aiLib kernel graph enum gen glue;
val batchl = read_pbbatchl "glue3512_batchl_dai04";
write_gluescript_batchl (selfdir ^ "/glue358_dai04_holmake") batchl;
*)

(* run script dai04
load "glue"; open aiLib kernel graph enum gen glue;
val scriptl = selfdir ^ "/glue358_dai04_holmake"

*)


(*
export TMPDIR="$PWD/tmp";
mkdir tmp;

load "glue"; open aiLib kernel graph enum gen glue;
fun g s = 
  let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
    (stinf s1, stinf s2)
  end;
val pbl_dai07 = map g (readl (selfdir ^ "/glue3512_pbl_dai07"));
val pbl_dai07_batch = mk_batch_full 


run_script_pbl (selfdir ^ "/glue3512_dai07") pbl_dai07;


load "glue"; open aiLib kernel graph enum gen glue;
fun g s = 
  let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
    (stinf s1, stinf s2)
  end;
val pbl_dai04 = map g (readl (selfdir ^ "/glue3512_pbl_dai04"));
run_script_pbl (selfdir ^ "/glue3512_dai04") pbl_dai04;

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
val parameterl9 = [(12,8,8,0.5)];
val parameterl11 = [(12,6,6,0.5)];
app (tune "bench11") parameterl11;

val parameterl12 = 
  [(0,8,0.5),(2,6,0.5),(1,8,0.5),(3,6,0.5),(2,8,0.5),(3,8,0.5)];
app (tune_3512 "bench12") parameterl12;

val parameterl14 = [(10,2,5,0.5),(10,3,5,0.5),(10,2,6,0.5)];
app (tune "bench14" 100) parameterl14;

val parameterl15 = [(4,0.5),(5,0.5),(6,0.5),(7,0.5),(8,0.5)];
app (tune_3510 "bench15" 100) parameterl15;

(* last 3 benchmarks *)

load "glue"; open aiLib kernel graph enum gen glue;
val enum358 = read_enum 8 (3,5);
val enum4416 = read_enum 16 (4,4);
benchmark "bench16_8_0_0" 200 enum358 enum4416;
val enum3512 = read_enum 12 (3,5);
val enum4412 = read_enum 12 (4,4);
benchmark "bench16_12_0_0" 200 enum3512 enum4412;
tune "bench16" 200 (8,4,0,0.5);
tune "bench16" 200 (8,0,0,0.5);

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

(* -------------------------------------------------------------------------
   Post-processing test
   ------------------------------------------------------------------------- *)

(*
load "glue"; open aiLib kernel graph enum gen glue;
val m1 = random_elem (read_par 10 (3,5));
val m2 = random_elem (read_par 14 (4,4));
val file = selfdir ^ "/test/test_script.sml";
write_script "test/testScript.sml" (m1,m2);
smlExecScripts.exec_script file;
*)


(* -------------------------------------------------------------------------
   Generating the dependencies (not necessary if one uses Holmake)
   ------------------------------------------------------------------------- *)

(* 
create a Holmafile in work_glue358 with INCLUDES=..

cd work_glue358

../../HOL/bin/genscriptdep r45_45753526901690_3583333758674368197732360914071565186738705964924502796773Theory.sig > ../template_ui

../../HOL/bin/genscriptdep r45_45753526901690_3583333758674368197732360914071565186738705964924502796773Theory.sml > ../template_uo

remove last line of template_uo
*)

(*
load "glue"; open aiLib kernel graph enum gen glue;

val template_ui = readl (selfdir ^ "/template_ui");
val template_uo = readl (selfdir ^ "/template_uo");

fun g s = 
  let val (s1,s2) = pair_of_list (String.tokens Char.isSpace s) in
    (stinf s1, stinf s2)
  end;
val glue358_pbl_dai07 = map g (readl (selfdir ^ "/glue358_pbl_dai07"));


fun write_dep_one dir (a,b) = 
  let 
    val file = dir ^ "/r45_" ^ infts a ^ "_" ^ infts b ^ "Theory"
  in
    writel (file ^ ".ui") (template_ui @ [file,file ^ ".sig"]);
    writel (file ^ ".uo") (template_uo @ [file,file ^ ".sml"])
  end;

val dir358 = "/local" ^ selfdir ^ "/work_glue358";
app (write_dep_one dir358) glue358_pbl_dai07;

val glue3510_pbl = 
  map g (readl (selfdir ^ "/glue3510_pbl_dai05")) @
  map g (readl (selfdir ^ "/glue3510_pbl_dai06"))
  ;

val dir3510 = "/local" ^ selfdir ^ "/work_glue3510";
app (write_dep_one dir3510) glue3510_pbl;

val glue3512_pbl = 
  map g (readl (selfdir ^ "/glue3512_pbl_dai04")) @
  map g (readl (selfdir ^ "/glue3512_pbl_dai07"));

val dir3512 = "/local" ^ selfdir ^ "/work_glue3512";
app (write_dep_one dir3512) glue3512_pbl;
*)

(* -------------------------------------------------------------------------
   Regrouping generalizations
   ------------------------------------------------------------------------- *)


(*
cp -r gen_bench16_8_4_0_0_5/* gen
cp -r gen_bench6_4_4_0_5/* gen
cp -r gen_bench12_12_0_8_0_5/* gen
*)


end (* struct *)




