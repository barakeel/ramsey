(* =========================================================================
   Communication with external sat solvers
   ========================================================================= *)
   
structure satio :> satio =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph glue
val ERR = mk_HOL_ERR "satio"

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

fun read_soll file = 
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

fun complete_graph (bsize,rsize) m = 
  let
    val file = selfdir ^ "/aaa_complete"
    val clausel = ramsey_clauses_mat (bsize,rsize) m
    val _ = write_dimacs file clausel
    val cmd = "cadical -q " ^ file ^ " > " ^ file ^ "_sol"
    val (_,t) = add_time (cmd_in_dir selfdir) cmd
  in
    case read_sol file of
      NONE => NONE
    | SOME sol => SOME (edgecl_to_mat (mat_size m) (sol @ mat_to_edgecl m))
  end;

(* 
load "satio"; load "enum"; 
open aiLib kernel graph enum glue satio;


val csize = 10;
val m1 = random_elem (enum.read_enum csize (3,5));
val m2 = random_elem (enum.read_enum (21 - csize) (4,4));
val m = diag_mat (unzip_mat m1) (unzip_mat m2);





  



load "nauty"; open nauty;
val mfulln = normalize_nauty mfull;
val m55 = diag_mat mfull (swap_colors mfull);

val bnl = neighbor_of 1 m55 0 @ (List.tabulate (11,fn x => x + 21));
val rnl = neighbor_of 2 m55 0 @ (List.tabulate (10,fn x => x + 32));

val bm = mat_permute (m55,length bnl) (mk_permf bnl);

val rm = mat_permute (m55,length rnl) (mk_permf rnl); print_mat rm;






val neighborl = List.tabulate (10,
mat_update_sym (m55,0,21,2





val clausel55 = ramsey_clauses_mat (5,5) m55;
write_dimacs "aaa_test55" clausel55;
val cmd = "cadical -q aaa_test55 > aaa_test55_sol";
val (_,t) = add_time (cmd_in_dir selfdir) cmd;


idea:
1) take a vertex (let's say vertex 1)
2) look at its neighbor in the 4,5 graph.
3) choose some of it neighbor in the 5,4 graph.

4) construct a completion of the new neigbhor 4,5 graph
5) 
let us say the first n in the complement
try to complete the graph if possible.

*)


end (* struct *)
