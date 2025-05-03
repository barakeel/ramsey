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
    case hd sl0 of
      "s SATISFIABLE" => SOME (read_sol_one d (tl sl0))
    | "s UNSATISFIABLE" => NONE
    | _ => raise ERR "read_sol" ""
  end

(* sometimes completion does not complete fully ?? *)
fun full m = ignore (assert null (all_holes m));


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

fun complete_graph (bluen,redn) m = 
  let
    val file = selfdir ^ "/aaa_complete"
    val statfile = selfdir ^ "/perf_stat_out"
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = write_dimacs file clausel
    val cmd = "perf stat -e instructions:u cadical -q " ^ 
      file ^ " > " ^ file ^ "_sol" ^ " 2> " ^ statfile
    val (_,t1) = add_time (cmd_in_dir selfdir) cmd
    val t2 = read_instructions statfile
  in
    case read_sol file of
      NONE => (NONE,(t1,t2))
    | SOME sol => 
      let val newm = edgecl_to_mat (mat_size m) (sol @ mat_to_edgecl m) in
        full newm; (SOME newm,(t1,t2))
      end
  end
  
(* -------------------------------------------------------------------------
   Model counter
   ------------------------------------------------------------------------- *)  

fun count_graph (bluen,redn) m = 
  let
    val file = selfdir ^ "/aaa_count"
    val clausel = ramsey_clauses_fast (bluen,redn) m
    val _ = nvaro_glob := SOME (number_of_holes m)
    val _ = write_dimacs file clausel
    val _ = nvaro_glob := NONE
    val cmd = "ganak --verb 0 " ^ file ^ " > " ^ file ^ "_out"
    val _ = cmd_in_dir selfdir cmd
    val sl = readl (file ^ "_out")
    val s1 = last (butlast sl)
    val s2 = last sl
    val _ = if not (String.isPrefix "c s exact arb int" s1)
            then raise ERR "count_graph" ""
            else ()
    val _ = if not (String.isPrefix "c o exact arb" s2)
            then raise ERR "count_graph" ""
            else ()
    val i1 = string_to_int (last (String.tokens Char.isSpace s1))
    val i2 = string_to_int (last (String.tokens Char.isSpace s2))
  in
    if i1 <> i2 then raise ERR "count_graph" "" else i1
  end

(* -------------------------------------------------------------------------
   Write sat problems (without edge correspondance) + 
   shift the indices by 1
   ------------------------------------------------------------------------- *)

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

fun read_plit s = 
  let val i = string_to_int s in 
    if i = 0 then NONE else SOME (Int.abs i - 1, i > 0) end;
  
fun read_pclause s =
  List.mapPartial read_plit (String.tokens Char.isSpace s)

fun read_pdimacs file = map (read_pclause) (readl file)

(* maybe: do this with edge variables *)
fun all_cones54 m = 
  let
    val cliqueb =  all_clique_mat m (blue,4)
    val clausel = map (map_assoc (fn _ => false)) cliqueb;
    val filein = selfdir ^ "/aaa_cones54"
    val fileout = filein ^ "_all"
    val filedebug = filein ^ "_debug"
    val _ = write_pdimacs filein clausel
    val cmd = "bdd_minisat_all " ^ filein ^ " " ^ fileout ^ " > " ^ filedebug
    val (_,t) = add_time (cmd_in_dir selfdir) cmd
  in
    read_pdimacs fileout
  end


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
    val m45b0 = valOf (fst (complete_graph (4,5) (diag_mat m35b m44b)))
    val m45b1 = mat_shift1 m45b0
    val mvb = mat_vertex0 nb nbb
    val m45b2 = valOf (mat_merge mvb m45b1)
    val m44r = swap_colors (unzip_mat (random_elem (enum.read_enum nrb (4,4))))
    val m53r = swap_colors (unzip_mat (random_elem (enum.read_enum nrr (3,5))))
    val m54r0 = valOf (fst (complete_graph (5,4) (diag_mat m44r m53r))) 
    val m54r1 = mat_shift1 m54r0
    val mvr = mat_vertex0 nr nrb
    val m54r2 = valOf (mat_merge mvr m54r1)
    val m55diag = diag_mat m45b2 m54r2
    val mv = mat_vertex0 size nb
    val m55 = valOf (mat_merge mv (mat_shift1 m55diag))
  in
    m55
  end
  
fun prove_cone (m45,m54) cone =
  let
    val m55 = diag_mat m45 m54;
    val edgecl = map (fn (x,b) => ((0,20+x), if b then 1 else 2)) cone;
    val m55cone = edgecl_to_mat (mat_size m55) edgecl;
    val m55e = valOf (mat_merge m55cone m55);
    val (r,t) = complete_graph (5,5) m55e
  in
    (m55e,(r,t))
  end

(* todo: make it faster to create the clauses *)
fun prove_55 m =
  let val (r,t) = complete_graph (5,5) m in
    (m,(r,t))
  end




(*
load "satio"; load "enum"; load "nauty"; load "gen";
open aiLib kernel graph enum glue satio nauty gen;
val ERR = mk_HOL_ERR "test";

val (m45,m54) = random_split (43,20,9,10);
(* todo: reveals the regions *)


val (l1,t) = add_time (all_clique_mat m55) (blue,5);
val (l3,t) = add_time (all_5cliques blue) m55;

val (conel,t1) = add_time all_cones54 m54;
val cone = random_elem conel;
val (m55e,(r,t2)) = prove_cone (m45,m54) cone;
print_mat m55e;

val mv = mat_vertex0 43 20;
val m55es1 = mat_shift1 m55e;
val m55f = valOf (mat_merge mv m55es1);

fun prepare_m m = 
  let 
    fun f (i,j) = 
      if i=j then 0 else 
      let val color = mat_sub (m,i,j) in
        if color = 0 then 3 else color
      end
  in
    mat_tabulate (mat_size m,f)
  end;
  
val m55f3 = prepare_m m55f;
val edgel = all_cedges m55f;


val (a,b) = random_elem edgel;
val mc = mat_copy m55f3;
val _ = mat_update_sym (mc,a,b,0);
val clb = all_5cliques blue mc;
val clr = all_5cliques red mc;
mat_sub (m55f3,a,b);
val (r,t) = add_time (count_graph (5,5)) mc;


fun count_gen m (a,b) =
  let
    val mc = mat_copy m
    val _ = mat_update_sym (mc,a,b,0)
    val (r,t) = add_time (count_graph (5,5)) mc;
  in
    ((a,b),r)
  end;

val edgerl = map (count_gen m55f3) edgel;

val edgerl2 = dict_sort compare_imax edgerl;

val x = length (filter (fn x => snd x > 1) edgerl);

fun prove_gen m edge =
  let
    val mc = mat_copy m
    val _ = mat_update_sym (mc,fst edge,snd edge,0)
    val (r,t) = add_time (complete_graph (5,5)) mc;
  in
    (mc,(r,t))
  end

(* 
todo use perf for comparing speeds 
todo do not generalize over impossible graphs?
*)

(* 
- better counting by enumerating solutions and removing duplicates 
- prevent from generalizing in the splits
(0,anything) or (1,<20) (20,>21)

*)


*)


end (* struct *)
