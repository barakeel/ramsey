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

fun is_small_lit n ((i,j),c) = i < n andalso j < n;
fun is_large_lit n ((i,j),c) = i >= n andalso j >= n;
fun is_middle_lit n x = not (is_small_lit n x) andalso not (is_large_lit n x);
fun get_small_lit l = filter (is_small_lit 10) l;
fun get_large_lit l = filter (is_large_lit 10) l;
fun get_middle_lit l = filter (is_middle_lit 10) l;
fun match_one m ((i,j),c) = mat_sub (m,i,j) = c;
fun match_all m clause = all (match_one m) clause;


val (clausel4524,t) = add_time (sat.ramsey_clauses_bare 24) (4,5);
val clausel4524i = number_snd 0 clausel4524;
val small0 = map_fst get_small_lit clausel4524i;
val large0 = map_fst get_large_lit clausel4524i; 
val middle = map get_middle_lit clausel4524;
fun score_one l = int_div 1 (int_pow 2 (length l));
val middlev = Vector.fromList (map score_one middle);
fun sum_middlev l = 
  let 
    val sum = ref 0.0
    fun f x = sum := !sum + Vector.sub (middlev,x) 
  in 
    app f l; !sum
  end;
  
val c1 = hd (read_enum 10 (3,5));
val d1 = hd (read_enum 14 (4,4));

fun score2 (a,b) =
  let
    val m1 = unzip_mat a;
    val small1 = map snd (filter (fn (clause,i) => match_all m1 clause) small0)
    val m2 = diag_mat (mat_empty 10) (unzip_mat b)
    val large1 = map snd (filter (fn (clause,i) => match_all m2 clause) large0)
    val inter1 = inter_increasing small1 large1
  in
    sum_middlev inter1
  end;
  

val (r,t) = add_time score2 (c1,d1);
val (r',t) = add_time score (c1,d1);

fun reduce_clause mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 
        then reduce_clause mat (lit :: acc) m
      else if color = newcolor 
        then reduce_clause mat acc m else NONE
    end;
 
val power2invv = 
  Vector.tabulate (11,fn x => 1.0 / Math.pow (2.0,Real.fromInt x));

fun len_clause_aux mat len clause = case clause of
    [] => len
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 
        then len_clause_aux mat (len + 1) m
      else if color = newcolor 
        then len_clause_aux mat len m 
      else 0
    end;
    
fun len_clause mat clause = len_clause_aux mat 0 clause;

fun sum_clausel mat clausel =
  let 
    val sum = ref 0.0
    fun f clause = 
      sum := Vector.sub (power2invv,len_clause mat clause) + (!sum)
  in
    app f clausel; !sum
  end
  
idea: compute the score for each problem 
      don't use the mapping from score to 

fun score (a,b) = 
  let 
    val m1 = diag_mat (mat_empty (mat_size a)) b
    val clausel = (List.mapPartial (reduce_clause m1 [])) clausel4525
    val _ = print_endline (its (length clausel4525) ^ " " ^ 
                           its (length clausel))
    val m2 = diag_mat a (mat_empty (mat_size b))
    val sc = sum_clausel m2 clausel;
  in
    1.0 / sc
  end;

timer_glob1 := 0.0;
timer_glob2 := 0.0;
val timel = map f sl2;
val timel' = map_fst (fn (m1,m2) => (unzip_mat m1, unzip_mat m2)) timel;
val (scorel,t) = add_time (map (fn (a,t) => (score a,t))) timel';
  
  
  
  
(* trying to find a corellation between speed and features *)
fun f s =
  let 
    val (sa,sb) = pair_of_list (String.tokens Char.isSpace s)
    val (sa1,sa2) = pair_of_list (String.tokens (fn x => x = #",") sa)
  in
    ((stinf sa1, stinf sa2), valOf (Real.fromString sb))
  end


val scorel_sorted = dict_sort (fst_compare Real.compare) scorel;

fun f (a,b) = rts a ^ " " ^ rts b;

app print_endline (map (rts o fst) scorel_sorted);
app print_endline (map (rts o snd) scorel_sorted);
*)

(* -------------------------------------------------------------------------
   Old scoring function easier to varies the parameter
   ------------------------------------------------------------------------- *)

(*
fun score (a,b) = 
  let 
    val m = diag_mat (unzip_mat a) (unzip_mat b)
    val clausel = List.mapPartial (reduce_clause m []) clausel4525;
    val lenl = map length clausel;
    val l = dlist (count_dict (dempty Int.compare) lenl)
    fun sc_one (a,b) = int_div b (int_pow 2 a)
  in
    sum_real (map sc_one l)
  end;
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


