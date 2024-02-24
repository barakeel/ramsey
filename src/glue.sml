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
   Overlap problem
   ------------------------------------------------------------------------- *)

fun overlap_clauses (par,cl) = 
  let 
    val holel = all_holes (unzip_mat par)
    val clall = nauty.all_inst_wperm par
    val cmp = cpl_compare IntInf.compare (list_compare Int.compare)
    val d = enew cmp cl
    val clnot = filter (fn x => not (emem x d)) clall
    fun f (c,perm) = 
      let 
        val m = unzip_mat c
        val newm = mat_permute (m,mat_size m) (mk_permf (invert_perm perm))
        fun g (a,b) = ((a,b), mat_sub (newm,a,b))
      in
        map g holel
      end
  in
    map f clnot
  end;

fun overlap_pb (bluen,redn) (p1,cl1) (p2,cl2) =
  let 
    val m = diag_mat (unzip_mat p1) (unzip_mat p2)
    val clausel = ramsey_clauses_mat (bluen,redn) m @ 
                  overlap_clauses (p1,cl1) @
                  overlap_clauses (p2,cl2)
  in
    satpb_of_clausel clausel
  end
  
fun glue_overlap (bluen,redn) (p1,cl1) (p2,cl2) =
  SAT_PROVE (overlap_pb (bluen,redn) (p1,cl1) (p2,cl2))

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
    val rl = smlParallel.parmap_queue_extern ncore benchspec () pbl
    fun f ((c1e,c2e),r) = infts c1e ^ "," ^ infts c2e ^ " " ^ rts r
    val mean = average_real rl
    val maxt = list_rmax rl
    val heads = String.concatWith " " (map rts [mean,maxt])
  in
    writel (dir ^ "/summary") [heads];
    writel (dir ^ "/sattime") (map f (combine (pbl,rl)))
  end
  


(*
export TMPDIR="$PWD/tmp";
mkdir tmp;
find /tmp -maxdepth 1 -type f -name 'MLTEMP*' ! -exec lsof {} \; -exec rm {} \;

load "glue"; open aiLib kernel graph glue;
load "enum"; open enum;
load "gen"; open gen;

val c1 = hd (read_cover 10 (3,5));
val c2 = hd (read_cover 14 (4,4));

val (_,t1) = add_time (glue_overlap (4,5) c1) c2;

val (_,t2) = add_time (glue (4,5) (fst c1)) (fst c2);
*)


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

val pbl1 = map (fst o f) sl2;

fun sgenx n b =
  let
    val m = unzip_mat b
    val edgel = sgen n (4,5) b
    fun f (a,b) = mat_update_sym (m,a,b,0)
    val _ = app f edgel
  in
    zip_mat m
  end;

val pbl2 = map_snd (sgenx 2) pbl1;
val expname = "e0e2";
benchmark_pbl "e0e2" pbl2;
readl (selfdir ^ "/exp/" ^ expname ^ "/summary");


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
    
mk_data "e0e2";

load "enum"; open aiLib kernel graph enum;


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
  end;


val enum3510 = read_enum 10 (3,5);
val enum4414 = read_enum 14 (4,4);

val clique35 = [(1,1),(2,1),(2,2),(3,2),(4,2)];
val clique44 = [(3,1),(2,1),(3,2),(2,2),(1,2)];

fun get_stats35 m = map (number_of_cliques m) clique35;
fun get_stats44 m = map (number_of_cliques m) clique44;

fun get_average35 enum =
  let val l = map (map snd o get_stats35 o unzip_mat) enum in
    map average_real (list_combine l)
  end;

fun get_average44 enum =
  let val l = map (map snd o get_stats44 o unzip_mat) enum in
    map average_real (list_combine l)
  end;
  
val average3510 = combine (clique35, get_average35 enum3510);
val average4414 = combine (clique44, get_average44 enum4414);

(* lower number is more difficult *)
fun difficulty stats35 stats45 =
  let 
    val l = combine (stats35,stats45)
    fun f (((n1,_),r1),((n2,_),r2)) = 
      r1 * r2 * (1.0 / Math.pow (2.0, Real.fromInt (n1 * n2)))
  in
    sum_real (map f l)
  end;
  
difficulty average3510 average4414; 
    
difficulty (get_stats35 (unzip_mat (hd enum3510))) average4414;

fun score3510 x = (x, difficulty (get_stats35 (unzip_mat x)) average4414);
fun score4414 x = (x, difficulty average3510 (get_stats44 (unzip_mat x)));

val enum3510sc = map score3510 enum3510;
val enum4414sc = map score4414 enum4414;

val enum3510sorted = dict_sort compare_rmax enum3510sc;
val enum4414sorted = dict_sort compare_rmax enum4414sc;



fun number_of_blueedges m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x = 1 then incr y else ()
  in
    mat_traverse f m; 
    !y
  end  



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

val e0e1sattime = read_sattime "e0e1";
val (e0e1score,t) = add_time (map_fst score) e0e1sattime;
val e0e1sorted = dict_sort (fst_compare Real.compare) e0e1score;
app print_endline (map (rts o fst) e0e1sorted);
app print_endline (map (rts o snd) e0e1sorted);

val e0e0sattime = read_sattime "e0e0bis";
val (e0e0score,t) = add_time (map_fst score) e0e0sattime;
val e0e0sorted = dict_sort (fst_compare Real.compare) e0e0score;
app print_endline (map (rts o fst) e0e0sorted);
app print_endline (map (rts o snd) e0e0sorted);


val d = dnew (cpl_compare IntInf.compare IntInf.compare) e0e0sattime;

fun find_inst_sc ((a,b),sc) =
  let 
    val instl = map fst (nauty.all_inst_wperm b)
    val candl = map (fn x => (a,x)) instl
    val cand = valOf (List.find (fn x => dmem x d) candl)
  in
    ((a,b),(sc,dfind cand d))
  end;
  
val l = map (snd o find_inst_sc) e0e1sattime;
fun f (a,b) = (b,a/b); 
val l1 = dict_sort (fst_compare Real.compare) (map f l);
app print_endline (map (rts o fst) l1);
app print_endline (map (rts o snd) l1);
*)

(* -------------------------------------------------------------------------
   Old scoring function easier to varies the parameter
   ------------------------------------------------------------------------- *)

(*

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
write_gluescripts "glue8" 1 (3,5,8) (4,4,16) (4,5);
*)

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


