(* =========================================================================
   Communication with external sat solvers
   ========================================================================= *)
   
structure satio :> satio =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph glue
val ERR = mk_HOL_ERR "satio"

(* -------------------------------------------------------------------------
   Exporting problems in the dimacs format (number the edges)
   ------------------------------------------------------------------------- *)

val nvaro_glob = ref NONE  

(* plain without edge mapping *)
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

fun complete_graph limito (bluen,redn) m = 
  let
    val dir = selfdir ^ "/sat_calls"
    val _ = mkDir_err dir
    val file = dir ^ "/cad_" ^ name_mat m
    val filemap = file ^ "_map"
    val filesol = file ^ "_sol"
    val filetim = file ^ "_tim"
    val filetim2 = file ^ "_tim2"
    fun clean () = app remove_file [file,filemap,filesol,filetim,filetim2]
    val _ = clean ()
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = write_dimacs file clausel
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
  in
    finalr
  end
  
  
fun complete_graph_all (bluen,redn) m = 
  let
    val dir = selfdir ^ "/sat_calls"
    val _ = mkDir_err dir
    val file = dir ^ "/bdd_" ^ name_mat m
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

val model_counter = "d4"

fun count_graph (bluen,redn) m = 
  let
    val dir = selfdir ^ "/sat_calls"
    val _ = mkDir_err dir
    val prefix = implode (first_n 3 (explode model_counter))
    val file = dir ^ "/" ^ prefix ^ "_" ^ name_mat m
    val filemap = file ^ "_map"
    val fileout = file ^ "_out"
    val filedbg = file ^ "_dbg"
    fun clean () = app remove_file [file,filemap,fileout,filedbg]
    val _ = clean ()
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = nvaro_glob := SOME (number_of_holes m)
    val _ = write_dimacs file clausel
    val _ = nvaro_glob := NONE
    val cmd = (if model_counter = "ganak" then "ganak --verb 0"
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
    val m45b0 = valOf (fst (complete_graph NONE (4,5) (diag_mat m35b m44b)))
    val m45b1 = mat_shift1 m45b0
    val mvb = mat_vertex0 nb nbb
    val m45b2 = valOf (mat_merge mvb m45b1)
    val m44r = swap_colors (unzip_mat (random_elem (enum.read_enum nrb (4,4))))
    val m53r = swap_colors (unzip_mat (random_elem (enum.read_enum nrr (3,5))))
    val m54r0 = valOf (fst (complete_graph NONE (5,4) (diag_mat m44r m53r))) 
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
  
fun enum_mcone m = complete_graph_all (5,5) (create_mcone m)
  
fun prove_cone m edgecl =
  let
    val mc1 = edgecl_to_mat (mat_size m) edgecl;
    val mc2 = valOf (mat_merge m mc1);
    val (ro,t) = complete_graph NONE (5,5) mc2
  in
    case ro of 
      SOME _ => raise ERR "prove_cone" "satisifiable"
    | NONE => t
  end

(* -------------------------------------------------------------------------
   Generalization
   ------------------------------------------------------------------------- *) 
   
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
fun count_gen m edgel =
  let
    val mc = erase_grey m
    fun f (i,j) = mat_update_sym (mc,i,j,0)
    val _ = app f edgel
    val r = count_graph (5,5) mc
  in
    r
  end

fun prove_gen limit mc holec gen =
  let
    val mch = mat_copy mc
    fun f (i,j) = mat_update_sym (mch,i,j,holec)
    val _ = app f gen
    val r = SOME (complete_graph (SOME limit) (5,5) mch)
                 handle ProofTimeout => NONE
  in
    case r of 
      SOME (SOME _, _) => raise ERR "prove_gen" "satisfiable"
    | SOME (NONE, t) => SOME t
    | NONE => NONE
  end
 
fun generalizable_edgel m mc =
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
    filter (not o is_splitting) (all_cedges mc)
  end;

fun loop_gen mc edgel (((gen,cover),(tr,ta)),sc) =
  let
    val limit = tr * 2.0
    val l1 = filter (fn x => not (mem x gen)) edgel
    val l2 = map (fn x => gen @ [x]) l1
    val (l3,t) = add_time (map_assoc (count_gen mc)) l2
    val l4 = filter (fn x => snd x > cover) l3
    val _ = log ("count: " ^ rts_round 2 t ^ " " ^ 
      its (length l4) ^ "/" ^ its (length l3))
    val (l5,t) = add_time (map_assoc (fn x => prove_gen limit mc 0 (fst x))) l4
    val _ = log ("prove: " ^ rts_round 2 t)
    val l6 = map_snd valOf (filter (fn x => isSome (snd x)) l5)
    fun score ((_,coverloc),(_,taloc)) = 
      IntInf.div (IntInf.fromInt taloc * IntInf.pow(10,100), coverloc)
    val l7 = dict_sort (snd_compare IntInf.compare) (map_assoc score l6)
  in
    if null l7 then (((gen,cover),(tr,ta)),sc) else
    let  
      val (((newgen,newcover),(newtr,newta)),newsc) = hd l7
      val _ = log (its (length newgen) ^ ": " ^
              string_of_edgel newgen ^ " " ^
              infts newcover ^ " " ^ rts_round 2 newtr ^ " " ^ 
              its newta ^ " " ^ infts sc)   
    in
      if sc < newsc then (((gen,cover),(tr,ta)),sc) else
      loop_gen mc edgel (hd l7)
    end 
  end;

(* -------------------------------------------------------------------------
   Generalization in parallel
   ------------------------------------------------------------------------- *) 

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

fun generalize limit mcone edgel =
  let
    val mcount = mk_mcount mcone edgel
    val (r1,_) = complete_graph NONE (5,5) mcount
  in
    case r1 of NONE => (IntInf.fromInt 0,0.0,0) | SOME _ =>
    let 
      val covera = count_graph (5,5) mcount
      val _ = if covera <= IntInf.fromInt 0 
        then raise ERR "generalize" "" else ()
      val mprove = mk_mprove mcone edgel
      val r2 = SOME (complete_graph (SOME limit) (5,5) mprove)
               handle ProofTimeout => NONE
    in
      case r2 of 
        NONE => (IntInf.fromInt (~1),0.0,0) 
      | SOME (_,(tr,ta)) => (covera,tr,ta)
    end
  end
  
fun generalize_string s =
  let 
    val (s1,s2,s3) = triple_of_list (String.tokens (fn x => x = #"|") s)
    val m = unzip_mat (stinf s1)
    val edgel = edgel_of_string s2
    val limit = streal s3
    val (covera,tr,ta) = generalize limit m edgel
  in
    String.concatWith " " [infts covera, rts tr, its ta]
  end

fun stats_list l1 =
  let
    val lconfig = filter (fn (_,(x,_,_)) => x = 0) l1
    val _ = log ("noconfig: " ^ its (length lconfig)) 
    val ltimeout = filter (fn (_,(x,_,_)) => x = ~1) l1
    val _ = log ("timeout: " ^ its (length ltimeout)) 
  in
    ()
  end
 
fun stats_best (((newgen,newcover),(newtr,newta)),newsc) =
  log (its (length newgen) ^ ": " ^
       string_of_edgel newgen ^ " " ^
       infts newcover ^ " " ^ rts_round 2 newtr ^ " " ^ 
       its newta ^ " " ^ infts newsc)   
 
fun para_loop_gen ncore mcone pool (((gen,cover),(tr,ta)),sc) =
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
    val l3 = map (fn (a,(b,c,d)) => ((a,b + cover),(c,d))) l2
    fun score ((_,coverloc),(_,taloc)) = 
      IntInf.div (IntInf.fromInt taloc * IntInf.pow(10,100), coverloc)
    val l4 = dict_sort (snd_compare IntInf.compare) (map_assoc score l3)
  in
    if null l4 then (((gen,cover),(tr,ta)),sc) else
    let  
      val best = hd l4
      val _ = stats_best best
    in
      if sc < snd best then (((gen,cover),(tr,ta)),sc) else
      para_loop_gen ncore mcone pool best
    end 
  end;

(*
load "satio"; load "enum"; load "nauty"; load "gen";
open aiLib kernel graph enum glue satio nauty gen;
val ERR = mk_HOL_ERR "test";

store_log := true;
logfile := selfdir ^ "/aaa_log_ramsey";
val _ = erase_file (!logfile);

val m55 = random_split (43,20,9,10);
val _ = log ("msplit: " ^ szip_mat m55);
val conel = enum_mcone m55;  
val cone = random_elem conel;
val (tr,ta) = prove_cone m55 cone;
val m55c = valOf (mat_merge m55 (edgecl_to_mat (mat_size m55) cone));
val _ = log ("mcone: " ^ szip_mat m55c);

val pool = generalizable_edgel m55 m55c;
fun score ((_,coverloc),(_,taloc)) = 
      IntInf.div (IntInf.fromInt taloc * IntInf.pow(10,100), coverloc);
val gen0 = (([]: (int * int) list,IntInf.fromInt 1),(tr,ta));
val sc = score gen0;

val r = para_loop_gen 64 m55c pool (gen0,sc);

val r = loop_gen m55c pool (gen0,sc);
*)


end (* struct *)
