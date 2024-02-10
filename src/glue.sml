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

fun ramsey_clauses_diagmat_bare (bluen,redn) m1 m2 =
  let val m = diag_mat (unzip_mat m1) (unzip_mat m2) in
    ramsey_clauses_mat (bluen,redn) m
  end

fun ramsey_clauses_diagmat (bluen,redn) m1 m2 =
  let val m = diag_mat (unzip_mat m1) (unzip_mat m2) in
    map satclause (ramsey_clauses_mat (bluen,redn) m)
  end

fun glue_pb (bluen,redn) m1i m2i =
  let val rclauses = ramsey_clauses_diagmat (bluen,redn) m1i m2i in
    mk_neg (list_mk_conj rclauses)
  end
  
fun glue (bluen,redn) m1i m2i = SAT_PROVE (glue_pb (bluen,redn) m1i m2i)

(* -------------------------------------------------------------------------
   Eliminating clauses with holes
   ------------------------------------------------------------------------- *)

fun shift_edgel x el = map (fn (a,b) => (a + x, b + x)) el;

fun diag_holes m1 m2 =
  let 
    val hole1 = all_holes m1  
    val hole2 = shift_edgel (mat_size m1) (all_holes m2)
  in
    hole1 @ hole2
  end
  
fun reduce_hole holed clause = 
  if exists (fn (edge,_) => emem edge holed) clause
  then SOME clause
  else NONE

fun glue_pb_hole (bluen,redn) m1i m2i =
  let 
    val clausel1 = ramsey_clauses_diagmat_bare (bluen,redn) m1i m2i 
    val holed = enew edge_compare (diag_holes (unzip_mat m1i) (unzip_mat m2i))
    val clausel2 = List.mapPartial (reduce_hole holed) clausel1
    val clausel3 = map satclause clausel2
  in
    mk_neg (list_mk_conj clausel3)
  end 

fun glue_hole (bluen,redn) m1i m2i = 
  SAT_PROVE (glue_pb_hole (bluen,redn) m1i m2i)




(*
load "glue"; open graph glue;
val m1 = hd (gen.read_par 10 (3,5));
val m2 = hd (gen.read_par 14 (4,4));

val thm = glue_hole (4,5) m1 m2;
../picosat-965/picosat aaa_test
*)
(* -------------------------------------------------------------------------
   Exporting problems in the dimacs format
   ------------------------------------------------------------------------- *)

fun glue_hole_ext (bluen,redn) m1i m2i =
  let 
    val clausel1 = ramsey_clauses_diagmat_bare (bluen,redn) m1i m2i 
    val holed = enew edge_compare (diag_holes (unzip_mat m1i) (unzip_mat m2i))
    val clausel2 = List.mapPartial (reduce_hole holed) clausel1
  in
    clausel2
  end   

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


