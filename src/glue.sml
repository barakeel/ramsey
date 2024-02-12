(* =========================================================================
   Glue generalized graphs with the help of cone clauses.
   ========================================================================= *)
   
structure glue :> glue =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph sat gen syntax
  minisatProve
val ERR = mk_HOL_ERR "glue"

(* -------------------------------------------------------------------------
   Create diagonal by block matrix and reduce the set of ramsey clauses
   ------------------------------------------------------------------------- *)

fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;

fun diag_mat m1 m2 = 
  let
    val ecl1 = mat_to_edgecl m1
    val ecl2 = shift_edgecl (mat_size m1) (mat_to_edgecl m2)
    val m = edgecl_to_mat (mat_size m1 + mat_size m2) (ecl1 @ ecl2)
  in
    m
  end
 
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

fun ramsey_clauses_diagmat (bluen,redn) m1 m2 =
  let val m = diag_mat (unzip_mat m1) (unzip_mat m2) in
    ramsey_clauses_mat (bluen,redn) m
  end

fun glue_pb (bluen,redn) m1i m2i =
  let val rclauses = map satclause 
    (ramsey_clauses_diagmat (bluen,redn) m1i m2i) 
  in
    mk_neg (list_mk_conj rclauses)
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
    writel (file ^ "_mapping") (map h mapping)
  end

(*
load "glue"; open aiLib kernel graph glue;
load "enum"; open enum;

val _ = mkDir_err "pico";
val csize = 10;
val m1 = random_elem (enum.read_enum csize (3,5));
val m2 = random_elem (enum.read_enum (24 - csize) (4,4));
val m2' = 
  zip_mat (random_subgraph (mat_size (unzip_mat m2) - 2) (unzip_mat m2));
writel "pico/test_mat"  (map infts [m1,m2,m2']);

val clausel = ramsey_clauses_diagmat (4,5) m1 m2';
val _ = write_dimacs "aaa_test" clausel;
val (_,t1) = add_time
  (cmd_in_dir selfdir) "../picosat-965/picosat -o aaa_test_out --all aaa_test";
val sl = readl "aaa_test_out";

*)
(*
(* take the first one example and extend it back. *)
load "glue"; open aiLib kernel graph glue;
val sl1 = first_n 6 (readl "aaa_test_out");


fun read_mapd file = 
  let 
    val sl = readl (file ^ "_mapping")
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

fun read_sol d sl =
  let
    val sl2 = map (fn x => tl (String.tokens Char.isSpace x)) sl
    val il3 = filter (fn x => x <> 0) (map string_to_int (List.concat sl2))
    fun f x = (dfind (Int.abs x) d : int * int, if x > 0 then 1 else 2)
  in
    map f il3
  end;

(* all variable should appear because there are cliques within unknown edges *)

fun read_solutions file = 
  let 
    val solfile = file ^ "_out"
    val mappingfile = file ^ "_mapping"
    val d = read_mapd file
    val sll0 = tl (butlast (readl "aaa_test_out"))
    val sll1 = rpt_split_sl "s SATISFIABLE" sll0      
  in
    map (read_sol d) sll1
  end 
   
val soll = read_solutions "aaa_test";

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


