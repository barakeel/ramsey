(* =========================================================================
   Glue generalized graphs with the help of cone clauses.
   ========================================================================= *)
   
structure satio :> satio =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph
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
   Reading the result of allsat problems
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
   Running picosat returning all satisfiable assignments
   ------------------------------------------------------------------------- *)

(* 
val file = "aaa_test"
val fileout = file ^ "_sol"
val picobin = selfdir ^ "/../picosat-965/picosat"
val cmd = picobin ^ " -o " ^ fileout ^ " --all " ^ file
*)

end (* struct *)
