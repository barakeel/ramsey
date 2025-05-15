(* =========================================================================
   Communication with external sat solvers
   ========================================================================= *)
   
structure satio :> satio =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph glue
val ERR = mk_HOL_ERR "satio"

type clause = coloring
type gen = ((edge list * IntInf.int) * (real * int)) * IntInf.int

(* -------------------------------------------------------------------------
   Exporting problems in the dimacs format (number the edges)
   ------------------------------------------------------------------------- *)

val nvaro_glob = ref NONE  

fun reduce_clause_aux mat acc clause = case clause of
    [] => SOME (rev acc)
  | (lit as ((i,j),color)) :: m => 
    let val newcolor = mat_sub (mat,i,j) in
      if newcolor = 0 
        then reduce_clause_aux mat (lit :: acc) m
      else if color = newcolor 
        then reduce_clause_aux mat acc m else NONE
    end
    
fun reduce_clause mat clause = reduce_clause_aux mat [] clause

fun reduce_clausel mat clausel = List.mapPartial (reduce_clause mat) clausel

(* plain without edge mapping and offsetting variable them by 1,
   use the standard encoding for clauses *)
fun write_pdimacs file clausel = 
  let
    val nvar = case !nvaro_glob of 
        NONE => list_imax (map fst (List.concat clausel)) + 1
      | SOME n => n
    fun g (i,b) = (if not b then "-" else "") ^ its (i+1)     
    fun f clause = String.concatWith " " (map g clause) ^ " 0"
    val header = "p cnf " ^ its nvar ^ " " ^ its (length clausel)
  in
    writel file (header :: map f clausel)
  end;

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
    val nvar = case !nvaro_glob of 
        NONE => dlength edged
      | SOME n => n
    val header = "p cnf " ^ its nvar ^ " " ^ its (length clausel)
    fun h ((i,j),v) = its i ^ "," ^ its j ^ " " ^ its v
  in
    writel file (header :: map f clausel);
    writel (file ^ "_map") (map h mapping)
  end

(* -------------------------------------------------------------------------
   Reading the result of satisfiable problems
   ------------------------------------------------------------------------- *)

fun read_plit s = 
  let val i = string_to_int s in 
    if i = 0 then NONE else SOME (Int.abs i - 1, i > 0) end;
  
fun read_pclause s =
  List.mapPartial read_plit (String.tokens Char.isSpace s)

fun read_pdimacs file = map (read_pclause) (readl file)

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
    val il1 = map (fn x => tl (String.tokens Char.isSpace x)) sl
    val il2 = List.concat il1
    val _ = if last il2 = "0" then () else raise ERR "read_sol_one" ""
    val il3 = map string_to_int (butlast il2)
    fun f x = (dfind (Int.abs x) d, if x > 0 then 1 else 2)
  in
    map f il3
  end

exception ProofTimeout

fun read_sol_cad file = 
  let 
    val d = read_map (file ^ "_map")
    val sl = readl (file ^ "_sol")
    val s = hd sl handle Empty => raise ProofTimeout
  in
    case s of
      "s SATISFIABLE" => SOME (read_sol_one d (tl sl))
    | "s UNSATISFIABLE" => NONE
    | _ => raise ProofTimeout
  end

fun read_sol_bdd file =  
  let 
    val d = read_map (file ^ "_map")
    val sl = readl (file ^ "_all")
    fun read_one s = 
      let 
        val il1 = String.tokens Char.isSpace s
        val _ = if last il1 = "0" then () else raise ERR "read_sol_bdd" ""
        val il2 = butlast il1
        val il3 = map string_to_int il2
        fun f x = (dfind (Int.abs x) d, if x > 0 then 1 else 2)
      in
        map f il3
      end
  in
    map read_one sl
  end

(* -------------------------------------------------------------------------
   Enumerate all ramsey clauses for a graph
   ------------------------------------------------------------------------- *)

fun all_pairs_f f l = case l of
    [] => ()
  | a :: m => (app (f a) m; all_pairs_f f m);

fun ramsey_clause m color clique = 
  let 
    val clause = ref []
    fun ramsey_lit i j =   
      let val newcolor = mat_sub (m,i,j) in
        if newcolor = 0 
          then clause := (if i < j then (i,j) else (j,i), color) :: !clause
        else if newcolor = color then ()
        else raise ERR "ramsey_clause" ""
      end
  in
    all_pairs_f ramsey_lit clique;
    rev (!clause)
  end
   
fun ramsey_clauses_fast (bluen,redn) m = 
  let 
    val clb = all_clique_mat m (blue,bluen)
    val clb2 = map (ramsey_clause m blue) clb
    val clr = all_clique_mat m (red,redn)
    val clr2 = map (ramsey_clause m red) clr
  in
    clb2 @ clr2
  end
   
(* -------------------------------------------------------------------------
   Calling solvers on ramsey clauses of a graph
   ------------------------------------------------------------------------- *)

val jobn_glob = ref NONE

fun mat_file prefix m = 
  let 
    val dir = selfdir ^ "/sat_calls"
    val _ = mkDir_err dir
    val name = if isSome (!jobn_glob) 
               then its (valOf (!jobn_glob)) 
               else name_mat m
  in
    dir ^ "/" ^ prefix ^ "_" ^ name
  end

fun read_instructions file = 
  let 
    val file2 = file ^ "2"
    val cmd = "awk '/instructions:u/ { gsub(\",\", \"\", $1); print $1 }' " ^
      file ^ " > " ^ file2
    val _ = cmd_in_dir selfdir cmd
    val t = string_to_int (hd (readl file2)) handle _ => valOf (Int.maxInt) 
  in
    t
  end 

(* checks that completion does complete fully *)
fun full m = 
  if null (all_holes m) then () else 
  print_endline "Warning: assignment not full";

fun satisfiable_err (mo,(tr,ta)) =
  if not (isSome mo) then () else 
  let val m = valOf mo in 
    mkDir_err (selfdir ^ "/satisfiable");
    writel (selfdir ^ "/satisfiable") ["satisfiable: " ^ szip_mat m];
    raise ERR "satisfiable_err" "satisfiable"
  end

fun complete_graph unsatb limito blockl (bluen,redn) m = 
  let
    val file = mat_file "cad" m
    val filemap = file ^ "_map"
    val filesol = file ^ "_sol"
    val filetim = file ^ "_tim"
    val filetim2 = file ^ "_tim2"
    fun clean () = app remove_file [file,filemap,filesol,filetim,filetim2]
    val _ = clean ()
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = write_dimacs file (clausel @ reduce_clausel m blockl)
    val precmd = case limito of NONE => "" | 
       SOME r => "timeout " ^  rts_round 3 r ^ " "
    val cmd =  precmd ^ "perf stat -e instructions:u cadical -q " ^ 
      file ^ " > " ^ filesol ^ " 2> " ^ filetim
    val (_,t1) = add_time (cmd_in_dir selfdir) cmd
    val _ = if not (exists_file filesol) 
            then (clean (); raise ProofTimeout) else ()
    val _ = if not (exists_file filetim) 
            then (clean (); raise ProofTimeout) else ()
    val t2 = read_instructions filetim
    val finalr =
      case (read_sol_cad file handle ProofTimeout => 
            (clean (); raise ProofTimeout)) 
      of
        NONE => (NONE,(t1,t2))
      | SOME sol => 
        let val newm = edgecl_to_mat (mat_size m) (sol @ mat_to_edgecl m) in
          full newm; (SOME newm,(t1,t2))
        end
    val _ = clean ()
    val _ = if unsatb then satisfiable_err finalr else ()
  in
    finalr
  end

fun complete_graph_all (bluen,redn) m = 
  let
    val file = mat_file "bdd" m
    val filemap = file ^ "_map"
    val fileall = file ^ "_all"
    val filedbg = file ^ "_dbg"
    fun clean () = app remove_file [file,filemap,fileall,filedbg]
    val _ = clean ()
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = write_dimacs file clausel
    val _ = app erase_file [fileall,filedbg]
    val cmd = "bdd_minisat_all " ^ file ^ " " ^ fileall ^ " > " ^ filedbg
    val _ = cmd_in_dir selfdir cmd
    val r = read_sol_bdd file
    val _ = clean ()
  in
    r
  end  

fun read_count fileout = 
  stinf (last (String.tokens Char.isSpace (last (readl fileout))))

val model_counter = "ganak"

fun write_count file blockl (bluen,redn) m =
  let
    val filemap = file ^ "_map"
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = nvaro_glob := SOME (number_of_holes m)
  in
    write_dimacs file (clausel @ reduce_clausel m blockl)
  end

fun count_graph blockl (bluen,redn) m = 
  let
    val prefix = implode (first_n 3 (explode model_counter))
    val file = mat_file prefix m
    val filemap = file ^ "_map"
    val fileout = file ^ "_out"
    val filedbg = file ^ "_dbg"
    fun clean () = app remove_file [file,filemap,fileout,filedbg]
    val _ = clean ()
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = nvaro_glob := SOME (number_of_holes m)
    val _ = write_dimacs file (clausel @ reduce_clausel m blockl)
    val _ = nvaro_glob := NONE
    val cmd = (if model_counter = "approxmc" then "approxmc --verb 0" 
               else if model_counter = "ganak" then "ganak --verb 0"
               else if model_counter = "d4" then "d4 -mc" else
               raise ERR "count_graph" model_counter) ^
              " " ^ file ^ " > " ^ fileout ^ " 2> " ^ filedbg
    val _ = cmd_in_dir selfdir cmd
    val count = read_count fileout 
    val _ = clean ()
  in
    count
  end

(* -------------------------------------------------------------------------
   Initial split with fixed degree for the three vertices
   ------------------------------------------------------------------------- *)

fun mat_shift1 m = 
  let 
    val size = mat_size m 
    val perm = List.tabulate (size, fn x => x + 1)  
  in
    mat_inject (size + 1) m perm
  end

fun mat_vertex0 size neigh =
  let
    fun f (i,j) = 
      if i = j then 0 
      else if i = 0 then (if j <= neigh then 1 else 2)
      else if j = 0 then (if i <= neigh then 1 else 2)
      else 0;
  in
    mat_tabulate (size,f)
  end

fun random_split (size,nb,nbb,nrb) = 
  let 
    val nr = size - nb - 1
    val nbr = nb - nbb - 1
    val nrr = nr - nrb - 1
    val m35b = unzip_mat (random_elem (enum.read_enum nbb (3,5)))
    val m44b = unzip_mat (random_elem (enum.read_enum nbr (4,4)))
    val m45b0 = valOf 
      (fst (complete_graph false NONE [] (4,5) (diag_mat m35b m44b)))
    val m45b1 = mat_shift1 m45b0
    val mvb = mat_vertex0 nb nbb
    val m45b2 = valOf (mat_merge mvb m45b1)
    val m44r = swap_colors (unzip_mat (random_elem (enum.read_enum nrb (4,4))))
    val m53r = swap_colors (unzip_mat (random_elem (enum.read_enum nrr (3,5))))
    val m54r0 = valOf 
      (fst (complete_graph false NONE [] (5,4) (diag_mat m44r m53r))) 
    val m54r1 = mat_shift1 m54r0
    val mvr = mat_vertex0 nr nrb
    val m54r2 = valOf (mat_merge mvr m54r1)
    val m55diag = diag_mat m45b2 m54r2
    val mv = mat_vertex0 size nb
    val m55 = valOf (mat_merge mv (mat_shift1 m55diag))
  in
    m55
  end
  
(* -------------------------------------------------------------------------
   Cones
   ------------------------------------------------------------------------- *)  
  
fun create_mcone m = 
  let 
    fun f (i,j) = 
      let val color = mat_sub (m,i,j) in
        if i = j then 0 else 
        if color = 0 then 3 else color
      end;
    val mc = mat_tabulate (mat_size m,f)
    val vl = neighbor_of red m 0
    val edgel = map (fn x => (1,x)) vl
    fun g m (i,j) = mat_update_sym (m,i,j,0)
  in
    app (g mc) edgel; mc
  end;

val degree_flag = false
  
fun enum_mcone m = 
  let 
    val conel = complete_graph_all (5,5) (create_mcone m)
    val bluen = length (neighbor_of blue m 1)
    val redn = length (neighbor_of red m 1)
    fun test cone = 
      let 
        val bn = length (filter (fn x => snd x = blue) cone)
        val rn = length (filter (fn x => snd x = red) cone)
      in
        bluen + bn < 25 andalso redn + rn < 25
      end
    val conel2 = if degree_flag then filter test conel else conel
    val conel3 = map (dict_sort (fst_compare edge_compare)) conel2
  in
    conel3
  end

(* -------------------------------------------------------------------------
   Generalization
   ------------------------------------------------------------------------- *) 

fun score_gen ((_,coverloc),(_,taloc)) = 
  IntInf.div (IntInf.fromInt taloc * IntInf.pow(10,100), coverloc)

fun erase_grey m = 
  let 
    fun f (i,j) = 
      if i=j then 0 else 
      let val color = mat_sub (m,i,j) in
        if color = 0 then 3 else color
      end
  in
    mat_tabulate (mat_size m,f)
  end
   
(* assumes 5,5: maybe count graph modulo iso by generating them
   and normalizing them instead *)
fun count_gen blockl m edgel =
  let
    val mcount = erase_grey m
    fun f (i,j) = mat_update_sym (mcount,i,j,0)
    val _ = app f edgel
    val r = count_graph blockl (5,5) mcount
  in
    r
  end

fun prove_gen limit blockl m holec gen =
  let
    val mh = mat_copy m
    fun f (i,j) = mat_update_sym (mh,i,j,holec)
    val _ = app f gen
    val r = SOME (complete_graph true (SOME limit) blockl (5,5) mh)
                 handle ProofTimeout => NONE
  in
    case r of 
      SOME (SOME _, _) => raise ERR "prove_gen" "satisfiable"
    | SOME (NONE, t) => SOME t
    | NONE => NONE
  end
 
fun generalizable_edgel m mcone =
  let 
    fun neighbore_of color graph x = 
      map (fn y => if x < y then (x,y) else (y,x)) 
        (neighbor_of color graph x);
    fun neighf m x = neighbore_of blue m x @ neighbore_of red m x;
    val va = hd (neighbor_of blue m 0);
    val vb = hd (neighbor_of red m 0);
    val neighl = neighf m 0;
    val neighla = filter (fn x => fst x <> 0) (neighf m va);
    val neighlb = filter (fn x => fst x <> 0) (neighf m vb);
    val neighd = enew edge_compare (neighl @ neighla @ neighlb);
    fun is_splitting (a,b) = emem (a,b) neighd;
  in
    filter (not o is_splitting) (all_cedges mcone)
  end;

fun loop_gen blockl m edgel (gene as (((gen,cover),(tr,ta)),sc)) =
  let
    val limit = tr * 2.0
    val l1 = filter (fn x => not (mem x gen)) edgel
    val l2 = map (fn x => x :: gen) l1
    val (l3,t) = add_time (map_assoc (count_gen blockl m)) l2
    val l4 = filter (fn x => snd x > cover) l3
    val _ = log ("count: " ^ rts_round 2 t ^ " " ^ 
      its (length l4) ^ "/" ^ its (length l3))
    val (l5,t) = add_time (map_assoc (fn x => 
      prove_gen limit blockl m 0 (fst x))) l4
    val _ = log ("prove: " ^ rts_round 2 t)
    val l6 = map_snd valOf (filter (fn x => isSome (snd x)) l5)
    val l7 = dict_sort (snd_compare IntInf.compare) (map_assoc score_gen l6)
  in
    if null l7 then gene else
    let  
      val newgene = hd l7
      val (((newgen,newcover),(newtr,newta)),newsc) = newgene
      val _ = log (its (length newgen) ^ ": " ^
              string_of_edgel newgen ^ " " ^
              infts newcover ^ " " ^ rts_round 2 newtr ^ " " ^ 
              its newta ^ " " ^ infts sc)
    in
      loop_gen blockl m edgel newgene
    end 
  end;

(* -------------------------------------------------------------------------
   Generalization in parallel
   ------------------------------------------------------------------------- *) 

fun mk_mcount_simple mcone edgel =
  let
    val _ = if null edgel then raise ERR "mk_mcount" "" else ()
    val mcount = erase_grey mcone
    fun f (i,j) = mat_update_sym (mcount,i,j,0)
    val _ = app f edgel
  in
    mcount
  end

fun mk_mcount mcone edgel =
  let
    val _ = if null edgel then raise ERR "mk_mcount" "" else ()
    val mcount = erase_grey mcone
    fun f (i,j) = mat_update_sym (mcount,i,j,0)
    val _ = app f (tl edgel)
    val (i,j) = hd edgel
    val color = mat_sub (mcount,i,j)
    val _ = if not (mem color [blue,red]) then raise ERR "mk_count" "" else ()
    val _ = mat_update_sym (mcount,i,j,3-color)
  in
    mcount
  end

fun mk_mprove mcone edgel =
  let
    val _ = if null edgel then raise ERR "mk_mprove" "" else ()
    val mprove = mat_copy mcone
    fun f (i,j) = mat_update_sym (mprove,i,j,0)
    val _ = app f edgel
  in
    mprove
  end

val nocount_flag = false

fun generalize limit blockl mcone edgel =
  let
    val mcount = mk_mcount mcone edgel
    val (r1,(tr',ta')) = complete_graph false NONE blockl (5,5) mcount
    val _ = print_endline ("filter: " ^ rts_round 2 tr')
  in
    case r1 of NONE => (IntInf.fromInt 0,0.0,0) | SOME _ =>
    let 
      val covera = if nocount_flag then 1 else count_graph blockl (5,5) mcount
      val _ = if (not nocount_flag andalso covera <= 0) 
        then raise ERR "generalize" "" else ()
      val mprove = mk_mprove mcone edgel
      val r2 = SOME (complete_graph true (SOME limit) blockl (5,5) mprove)
               handle ProofTimeout => NONE
    in
      case r2 of 
        NONE => (IntInf.fromInt (~1),0.0,0) 
      | SOME (SOME m, (tr,ta)) => raise ERR "generalize" "satisfiable"
      | SOME (NONE,(tr,ta)) => 
         (print_endline ("prove: " ^ rts_round 2 tr');
         (covera,tr,ta))
    end
  end
  
(* todo pass the blocking clauses *)
fun generalize_string s =
  let 
    val (s1,s2,s3) = triple_of_list (String.tokens (fn x => x = #"|") s)
    val m = unzip_mat (stinf s1)
    val edgel = edgel_of_string s2
    val limit = streal s3
    val (covera,tr,ta) = generalize limit [] m edgel
  in
    String.concatWith " " [infts covera, rts tr, its ta]
  end

fun stats_list l =
  let
    val l1 = filter (fn (_,(x,_,_)) => x > 0) l
    val l2 = filter (fn (_,(x,_,_)) => x = 0) l
    val l3 = filter (fn (_,(x,_,_)) => x < 0) l
  in
    log ("positive count: " ^ its (length l1) ^
         ", null count: " ^ its (length l2) ^
         ", timeout: " ^ its (length l3))
  end
 
fun stats_best (((newgen,newcover),(newtr,newta)),newsc) =
  log (its (length newgen) ^ ": " ^
       string_of_edgel newgen ^ " " ^
       infts newcover ^ " " ^ rts_round 2 newtr ^ " " ^ 
       its newta ^ " " ^ infts newsc)   
 
fun para_loop_gen ncore mcone pool (genorg as (((gen,cover),(tr,ta)),sc)) =
  let
    val limit = tr * 2.0
    val pool' = filter (fn x => not (mem x gen)) pool
    val genl = map (fn x => x :: gen) pool'
    val _ = log ("candidates: " ^ its (length genl)) 
    fun f x = infts (zip_mat mcone) ^ "|" ^ string_of_edgel x ^ "|" ^ rts limit
    val slin = map f genl
    val (slout,t) = add_time (parmap_sl ncore "satio.generalize_string") slin
    val _ = log ("parmap_sl: " ^ rts_round 2 t)
    fun g s = 
      let val (s1,s2,s3) = triple_of_list (String.tokens Char.isSpace s) in
        (stinf s1, streal s2, string_to_int s3)
      end
    val l1 = map_snd g (combine (genl,slout))
    val _ = stats_list l1
    val l2 = filter (fn (_,(x,_,_)) => x > 0) l1
    val l3 = map (fn (a,(b,c,d)) => ((a, 
      if nocount_flag then cover * 2 else b + cover),(c,d))) l2
    fun score (gen as ((_,coverloc),(trloc,taloc))) = 
      if nocount_flag 
      then IntInf.fromInt taloc
      else score_gen gen
    val l4 = dict_sort (snd_compare IntInf.compare) (map_assoc score l3)
    val _ = print_endline (its (length l4))
  in
    if null l4 then (print_endline "end1"; genorg) else
    let  
      val best = hd l4
      val newtr = fst (snd (fst best))
      val _ = stats_best best
    in
      if (not nocount_flag andalso sc < snd best) orelse
         (nocount_flag andalso newtr > 20.0)
      then (print_endline "end2"; genorg)
      else para_loop_gen ncore mcone pool best
    end 
  end;

(* -------------------------------------------------------------------------
   Proving in parallel
   ------------------------------------------------------------------------- *) 

(* todo: add block clauses *)
fun prove_graph_string s =
  let val (ro,(tr,ta)) = complete_graph true NONE [] (5,5) (sunzip_mat s) in
    case ro of 
      SOME _ => String.concatWith " " ["sat",rts tr,its ta]
    | NONE => String.concatWith " " ["unsat",rts tr,its ta]
  end

fun read_prove_graph s = 
  let val (s1,s2,s3) = triple_of_list (String.tokens Char.isSpace s) in
    (s1,streal s2,string_to_int s3)
  end 

fun add_cone m cone = 
  valOf (mat_merge m (edgecl_to_mat (mat_size m) cone))

fun para_prove_cone ncore m =
  let 
    val dir = selfdir ^ "/result"
    val _ = mkDir_err dir
    val mem = !logfile
    val _ = logfile := dir ^ "/cone_" ^ name_mat m ^ "_log"
    val (conel,t) = add_time enum_mcone m
    val _ = log ("cone: " ^ its (length conel) ^ " " ^ rts_round 2 t)
    val ml = map (szip_mat o add_cone m) conel
    val (sl,t) = add_time (parmap_sl ncore "satio.prove_graph_string") ml
    val _ = log ("prove: " ^ rts_round 2 t)
    val rl = map read_prove_graph sl
    val lunsat = filter (fn (x,_,_) => x = "unsat") rl
    val lsat = filter (fn (x,_,_) => x = "sat") rl
    val _ = log ("total: " ^ its (length rl) ^ 
                 ", unsat: " ^ its (length lunsat) ^
                 ", sat: " ^ its (length lsat))
    val _ = logfile := mem
    val msl = map (fn (a,b) => a ^ " " ^ b) (combine (ml,sl))
  in
    writel (selfdir ^ "/result/cone_" ^ name_mat m ^ "_res") msl
  end
 
(* -------------------------------------------------------------------------
   Selecting cone with shortest time for generalization
   ------------------------------------------------------------------------- *) 

(* assumes edges in clauses are ordered *)
fun subsumes clause1 clause2 = case (clause1,clause2) of
    ([],_) => true
  | (_,[]) => false
  | ((e1,c1) :: m1, (e2,c2) :: m2) =>
    (
    case edge_compare (e1,e2) of
      EQUAL => if c1 <> c2 then false else subsumes m1 m2 
    | LESS => false
    | GREATER => subsumes clause1 m2
    )

fun select_cone (ncone,tim) blockl m conel = 
  let
    val sel = random_subset ncone conel
    fun f cone = SOME (complete_graph true (SOME tim) blockl (5,5) 
      (add_cone m cone)) handle ProofTimeout => NONE
    val rl = map_assoc f sel
    val rl0 = filter (isSome o snd) rl
  in
    if null rl0 then select_cone (ncone, 2.0 * tim) blockl m conel else
    let
      val rl2 = map_snd (snd o valOf) rl0
      val rl3 = dict_sort (snd_compare (snd_compare Int.compare)) rl2;
      val _ = if null rl3 then raise ERR "" "" else ();
      val (cone,(tr,ta)) = hd rl3;
      val gen0 = (([]: (int * int) list,IntInf.fromInt 1),(tr,ta));
      val sc = score_gen gen0
    in 
      (cone,(gen0,sc))
    end
  end

fun mk_block mcone pool (gen:gen) =
  let 
    val block1 = list_diff pool ((fst o fst o fst) gen)
    val block2 = map_assoc (fn (i,j) => mat_sub (mcone,i,j)) block1
  in
    dict_sort (fst_compare edge_compare) block2
  end
 
fun prove_conel pool m blockl conel =
  if null conel then print_endline "Unsatisfiable" else
  let
    val _ = log ("cones: " ^ its (length conel))
    val ((cone,gen),t) = add_time (select_cone (10,0.5) [] m) conel
    val _ = log ("select: " ^ rts_round 2 t ^ " " ^ string_of_edgecl cone)
    val (newgen,t) = add_time (loop_gen blockl (add_cone m cone) pool) gen
    val _ = log ("generalize: " ^ rts_round 2 t)
    val block = mk_block (add_cone m cone) pool newgen
    val _ = log ("block: " ^ string_of_edgecl block)
    val newconel = filter (not o subsumes block) conel
    val _ = log ("covered: " ^ its (length conel - length newconel))
    val newblockl = block :: blockl
  in
    prove_conel pool m newblockl newconel 
  end


(* -------------------------------------------------------------------------
   Monte carlo model counter
   ------------------------------------------------------------------------- *) 

val counter = ref 0

fun is_sat m = 
  isSome (fst (complete_graph false (SOME 1.0) [] (5,5) m))  
  handle ProofTimeout => (incr counter; false)
  
fun sample_one m ((i,j),c) =
  let 
    val _ = if mat_sub (m,i,j) <> 0 
            then raise ERR "sample_one" "not a hole"
            else ()
    val mb = mat_tabulate (mat_size m, fn (i',j') =>
       if (i',j') = (i,j) then blue else mat_sub (m,i',j'))
    val mr =  mat_tabulate (mat_size m, fn (i',j') =>
       if (i',j') = (i,j) then red else mat_sub (m,i',j'))
    val mbsat = is_sat mb 
    val mrsat = is_sat mr
  in
    case (mbsat,mrsat) of
      (true,true) => (true, SOME (if c=blue then mb else mr))
    | (true,false) => (false, SOME mb)
    | (false,true) => (false, SOME mr)
    | (false,false) => (false, NONE)
  end

fun sample_loop nchoice m edgecl = case edgecl of 
    [] => (SOME m,nchoice) 
  | edgec :: cont => 
    let val _ = print_endline (its nchoice ^ "/" ^ its (length edgecl)) in
      case sample_one m edgec of
          (_, NONE) => (NONE, nchoice) 
        | (b, SOME newm) => 
          sample_loop (if b then nchoice + 1 else nchoice) newm cont
    end

fun sample mcone edgecl = 
  let 
    val mmax = mk_mcount_simple mcone (map fst edgecl) 
    val _ = counter := 0
    val r = sample_loop 0 mmax edgecl
  in
    print_endline ("timeout: " ^ its (!counter)); 
    counter := 0;
    r
  end
  
fun szip_mato mato = case mato of
    NONE => its (~1)
  | SOME m => szip_mat m
 
fun sunzip_mato s =
  let val i = stinf s in 
    if i < 0 then NONE else SOME (unzip_mat i)
  end
 
fun sample_string s =
  let 
    val _ = print_endline "hi"
    val (s1,s2,s3) = split_triple #"|" s
    val mcone = sunzip_mat s1
    val edgecl = edgecl_of_string s2
    val jobn = string_to_int s3
    val _ = jobn_glob := SOME jobn
    val (minsto,nchoice) = sample mcone edgecl
  in
    String.concatWith " " [szip_mato minsto, its nchoice] 
  end

local open IntInf in
  fun sum_inf il = case il of [] => 0 | a :: m => a + sum_inf m
  fun average_inf il = sum_inf il div (IntInf.fromInt (length il))
end

(* todo give more info on the number of time a branch was 
   avoided because of timeout *)
fun para_sample ncore nsample m edgel = 
  let 
    val ms = szip_mat m
    fun random_edgecl () = 
      shuffle (map_assoc (fn x => random_int (1,2)) edgel)
    val edgecll = List.tabulate (nsample, fn _ => random_edgecl ())
    val slin = map (fn (x,jobn) => 
       ms ^ "|" ^ string_of_edgecl x ^ "|" ^ its jobn) (number_snd 0 edgecll)
    val (slout,t) = add_time (parmap_sl ncore "satio.sample_string") slin 
    fun read s = 
       let val (s1,s2) = split_pair #" " s in
         (sunzip_mato s1, string_to_int s2)
       end
    val rl = map read slout
    fun pow2 x = IntInf.pow (2,x)
    val r = average_inf (map (pow2 o snd) rl)
    val terml = filter (isSome o fst) rl
    val _ = log ("sample: " ^ its nsample ^ 
                 "completed: " ^ its (length terml) ^
                 ", average: " ^ IntInf.toString r)
    val _ = mkDir_err (selfdir ^ "/result")
    val _ = writel (selfdir ^ "/result/sample_" ^ name_mat m) slout  
  in
    r
  end
    
(*
load "satio"; load "enum"; load "nauty"; load "gen";
open aiLib kernel graph enum glue satio nauty gen;
val ERR = mk_HOL_ERR "test";

logfile := selfdir ^ "/aaa_log_ramsey";
val _ = erase_file (!logfile);

val m55 = random_split (43,20,9,10);
val _ = log ("msplit: " ^ szip_mat m55);
val conel = enum_mcone m55;  
val cone = random_elem conel;
val m55c = add_cone m55 cone
val (_,(tr,ta)) = complete_graph true NONE [] (5,5) m55c

val _ = log ("mcone: " ^ szip_mat m55c);

val pool = generalizable_edgel m55 m55c;
fun score ((_,coverloc),(_,taloc)) = 
      IntInf.div (IntInf.fromInt taloc * IntInf.pow(10,100), coverloc);
val gen0 = (([]: (int * int) list,IntInf.fromInt 1),(tr,ta));
val sc = score gen0;

val r = para_loop_gen 64 m55c pool (gen0,sc);
val r = loop_gen m55c pool (gen0,sc);
*)

(*
load "satio"; load "enum"; load "nauty"; load "gen";
open aiLib kernel graph enum glue satio nauty gen;
val ERR = mk_HOL_ERR "test";
val m55 = sunzip_mat (hd (readl (selfdir ^ "/aaa_split")));
val m55cone = sunzip_mat (hd (readl (selfdir ^ "/aaa_mcone")));


val edgelgen = edgel_of_string
"35-40 38-42 34-35 29-34 37-39 22-37 22-26 30-36 29-37 25-40 36-40 32-39 27-28 30-40 25-32 32-36 34-38 25-37 27-36 36-37 32-37 32-42 28-38 23-33 39-42 23-35 28-33 33-40 25-28 23-28 28-31 35-39 33-41 30-39 23-39 36-39 33-39 24-32 38-41 27-32 39-40 31-36 31-39 31-41 27-41 31-32 27-33 11-17 16-20 26-37 33-36 28-39 37-38 23-36 37-41 31-40 22-31 32-34 23-31 32-41 38-39 37-42 32-38 28-36 29-39 31-38 26-32 23-32 30-37 31-34 22-32 28-35 27-39 24-39 13-17 15-18 34-39 11-20 26-28 25-39 23-30 26-38 32-40 23-40 31-33 22-28 15-17 29-32 28-32 28-37 35-37 31-37 33-35 22-39 38-40 31-35 22-40 24-31 28-40 5-8 7-18 9-18 7-9 5-10 28-30 26-39 19-20 8-10 4-6 3-7 2-15 5-14 4-7 6-11 4-10 7-12 22-29 23-38 5-9 2-17 30-33 9-10 33-37 22-33 5-18 8-20 2-14 24-33 3-19 33-42 8-15 8-13 25-33 29-35 4-11 2-6 4-19 8-18 16-18 4-15 23-29 2-3 28-29 13-18 4-12 6-10 9-15 9-13 5-15 12-17 5-11 14-15 28-41 3-20 2-18 30-32 25-35 12-18 12-19 14-18 4-8 6-7 3-8 5-16 3-17 16-19 10-13 6-9 10-12 7-8 5-6 3-6 4-17 10-15 6-15 3-18 7-10 6-18 3-4 9-17 3-14 4-18 6-17 9-12 11-19 2-5 10-14 33-38 4-9 5-20 17-19 9-14 6-12 6-19 2-7 2-20 14-17 28-42 2-19 3-15 25-31 2-11 18-19 7-19 5-7 2-12 26-33 29-31 4-20 29-30 2-16 22-38 4-16 6-8 3-9 7-13 31-42 28-34 8-9 29-38 8-12 7-14 17-18 5-12 6-14 8-16 3-10 8-19 8-11 35-36 2-9 9-11 6-20 5-19 29-33 15-20 10-16 2-8 14-19 26-34 11-18 34-37 5-13 1-28 6-16 9-16 7-20 10-17 7-17 4-14 10-11 2-13 2-10 7-11 8-17 2-4 5-17 1-31 39-41 13-19 33-34 7-16 12-15 3-13 32-35 3-5 1-39 30-31 36-38 7-15 10-18 27-31 17-20 26-31 23-26 24-28 24-37 1-37 1-33 32-33 9-20 16-17 8-14 22-24 10-19 3-12 4-13 10-20 15-19 6-13 3-11 3-16 9-19 4-5 1-32 1-40 18-20 23-42";

val ncore = 64;
val nsample = 64;
val r = para_sample ncore nsample m55cone edgelgen;

val edgeclgen = shuffle (map_assoc (fn x => random_int (1,2)) edgelgen);
val (n,t) = add_time (sample m55cone) edgeclgen; 





val r = sample_one m (hd edgeclgen);

108

String.size (IntInf.toString (IntInf.pow (2,107)));
10^33 / 10^9;

10^24;




fun mk_sample mcount n =
  let
    val edgel = random_subset n all_holes
    val msample = mat_copy mcount
    fun f (i,j) = mat_update_sym (mcount,i,j,random_int (1,2))
    val _ = app f edgel
  in
    
  end

fun f n = 
  let val mcount = mk_mcount_simple m55cone (first_n n (rev edgelgen)) in
    write_count (selfdir ^ "/count/" ^ its n) [] (5,5) mcount
  end;

app f (List.tabulate (length edgelgen - 1,fn x => x + 1));

val bl = neighbor_of blue m55 0;
val rl = neighbor_of red m55 0;
val bbl = filter (fn x => x <> 0) (neighbor_of blue m55 (hd bl));
val brl = filter (fn x => x <> 0) (neighbor_of red m55 (hd bl));
val rbl = filter (fn x => x <> 0) (neighbor_of blue m55 (hd rl));
val rrl = filter (fn x => x <> 0) (neighbor_of red m55 (hd rl));

(* constraints *)
fun enc_permv (i,j) = i * (mat_size m55) + j;
fun pos_lit i = (i,true);
fun neg_lit i = (i,false);

fun perm_clause vl = 
  let 
    val clause = map pos_lit vl
    val clausel = map (fn (x,y) => [neg_lit x, neg_lit y]) (all_pairs vl)
  in
    clause :: clausel
  end;
 
 val lit_compare = cpl_compare Int.compare bool_compare;
val clause_compare = list_compare lit_compare
fun sort_clause clause = dict_sort lit_compare clause;
fun mk_clause_set clausel = 
  mk_sameorder_set clause_compare (map sort_clause clausel);

fun perm_clauses il = 
  let 
    fun f (i,il) = map (fn j => (i,j)) il
    val horl = map f (map (fn i => (i,il)) il);
    val verl = map (map swap) horl;
    val linel = map (map enc_permv) (horl @ verl);
    val clausel = List.concat (map perm_clause linel);
  in
    mk_clause_set clausel
  end;

val clausel_perm = List.concat 
  (map perm_clauses [[0],[hd bl],[hd rl],bbl,brl,rbl,rrl]);



fun class_of v = 
  if v = 0 then 0
  else if v = hd bl then 1
  else if v = hd rl then 2
  else if mem v bbl then 3
  else if mem v brl then 4
  else if mem v rbl then 5
  else if mem v rrl then 6
  else raise ERR "class_of" "";

val edgelall = generalizable_edgel m55 m55cone;
val edgeclall = map (fn (i,j) => ((i,j),mat_sub (m55cone,i,j))) edgelall;
val edgelkept = list_diff edgelall edgelgen;
val edgeclkept = map (fn (i,j) => ((i,j),mat_sub (m55cone,i,j))) edgelkept;

fun renumber clausel = 
  let 
    val varl = mk_fast_set Int.compare (map fst (List.concat clausel))
    val d = dnew Int.compare (number_snd 0 varl)
    fun f clause = map_fst (fn x => dfind x d) clause
  in
    map f clausel
  end;
  
fun clauses_of_match (((i1,j1),c1),((i2,j2),c2)) =
  let 
    val clause1 =
      if class_of i1 = class_of i2 andalso
         class_of j1 = class_of j2 andalso
         c1 <> c2
      then [[neg_lit (enc_permv (i1,i2)), neg_lit (enc_permv (j1,j2))]]
      else []
    val clause2 =
      if class_of i1 = class_of j2 andalso
         class_of j1 = class_of i2 andalso
         c1 <> c2
      then [[neg_lit (enc_permv (i1,j2)), neg_lit (enc_permv (j1,i2))]]
      else [] 
  in
    clause1 @ clause2
  end
  
  
fun number_of_var clausel = length 
  (mk_fast_set Int.compare (map fst (List.concat clausel)));
  
val vnl1 = map (number_of_var o perm_clauses) [[0],[hd bl],[hd rl],bbl,brl,rbl,rrl];

val clausel_match = List.concat (map clauses_of_match ((cartesian_product edgeclall edgeclkept)));  

val clausel = mk_clause_set (clausel_perm @ clausel_match);

write_pdimacs (selfdir ^ "/aaa_test") (renumber clausel);
  
553648128  
494927872


*)


(* statistics
val sl = readl (selfdir ^ "/result/" ^ "cone_N_OKsp_1Y42FHAbYorYbQD_49qO4b36GRrdUoJxiP8XuP9_a6v9YWGPsOI6m-tFy3UtVQrBQRX8UO1KHI1cHPU546bHMum-liP1uN68wQW8fX-cVWT_tAa-x-2S6nMbqSIE4EBc-Pj8WeOwV6Svs0cjMw8q6MWiUqAeAPfNSoV5rJPPz2y34oYYPO9-wa_31mj9OKM8v7E50_eULiVjcXPFCVL0HeQ2lAoR59KhEmOC4h5t_res");
length sl;

fun f x = 
  let val (a,b,c,d) = quadruple_of_list (String.tokens Char.isSpace x) in
    streal c
  end;

val rl = map f sl;
val interval = [0.0,0.25,0.5,1.0,2.0,4.0,8.0,16.0,32.0,64.0,128.0];
fun mk_interval l = case l of
    [] => []
  | [a] => [(a,1000000000000000.0)]
  | a :: b :: m => (a,b) :: mk_interval (b :: m);
val il = mk_interval interval;
fun f (a,b) = length (filter (fn x => x >= a andalso x < b) rl);

val il1 = map_assoc f il;


val rl = filter (fn x => x < 0.5) rl; length rl1;
val rl1 = filter (fn x => x >= 0.5 andalso x < 1) rl;
*)

(*
load "satio"; load "enum"; load "nauty"; load "gen";
open aiLib kernel graph enum glue satio nauty gen;
val ERR = mk_HOL_ERR "test";


store_log := true;
logfile := selfdir ^ "/aaa_log_ramsey_nocount";
val _ = erase_file (!logfile);

val (m55s,m55cs) = pair_of_list (readl (selfdir ^ "/aaa_m_1"));
val m55 = sunzip_mat m55s;
val m55c = sunzip_mat m55cs;
val pool = generalizable_edgel m55 m55c;

val gen0 = ((([]: (int * int) list,arb1),(0.5,valOf (Int.maxInt))),arb0);
val edgel = edgel_of_string "28-42 2-19 3-15 25-31 2-11 18-19 7-19 5-7 2-12 26-33 29-31 4-20 29-30 2-16 22-38 4-16 6-8 3-9 7-13 31-42 28-34 8-9 29-38 8-12 7-14 17-18 5-12 6-14 8-16 3-10 8-19 8-11 35-36 2-9 9-11 6-20 5-19 29-33 15-20 10-16 2-8 14-19 26-34 11-18 34-37 5-13 1-28 6-16 9-16 7-20 10-17 7-17 4-14 10-11 2-13 2-10 7-11 8-17 2-4 5-17 1-31 39-41 13-19 33-34 7-16 12-15 3-13 32-35 3-5 1-39 30-31 36-38 7-15 10-18 27-31 17-20 26-31 23-26 24-28 24-37 1-37 1-33 32-33 9-20 16-17 8-14 22-24 10-19 3-12 4-13 10-20 15-19 6-13 3-11 3-16 9-19 4-5 1-32 1-40 18-20 23-42";
val gen101 = (((edgel,arb1),(0.33,1)),arb0);

val r = para_loop_gen 64 m55c pool gen101;

*)


end (* struct *)
