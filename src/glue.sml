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

fun satlit ((i,j),c) = 
   if c = 1 then satvar i j
   else if c = 2 then mk_neg (satvar i j)
   else raise ERR "satlit" "unexpected"

fun invsatlit ((i,j),c) = 
   if c = 2 then satvar i j
   else if c = 1 then mk_neg (satvar i j)
   else raise ERR "satlit" "unexpected"

fun satclause clause = list_mk_disj (map invsatlit clause)

fun ramsey_clauses_mat (bluen,redn) mat =
  List.mapPartial (reduce_clause mat []) 
    (ramsey_clauses_bare (mat_size mat) (bluen,redn));

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


(* test
load "glue"; open aiLib kernel graph syntax sat gen glue;

val m4412l = read_cover 12 (4,4);
val l = List.concat (map snd m4412l);
val l2 = map fst l;
val l3 = mk_fast_set IntInf.compare l2;
length l3;



fun apply_coloring m edgecl = 
   let 
     val newm = mat_copy m
     fun f ((i,j),c) = mat_update_sym (newm,i,j,c) 
   in
     app f edgecl; newm
   end

fun all_coloring edgel = 
  let
    val edgebothl =
      let 
        val l = ref []
        fun f (i,j) = l := [((i,j),blue),((i,j),red)] :: !l 
      in 
        (app f edgel; !l)
      end
  in
    cartesian_productl edgebothl
  end

load "nauty"; open nauty;

fun all_leafs m =
  let
    val _ = print "."
    val edgel = all_holes m
    val coloringltop = all_coloring edgel
    val d = ref (dempty IntInf.compare)
    fun loop d coloringl = case coloringl of 
        [] => d
      | coloring :: cont =>
        let val child = zip_mat (normalize_nauty (apply_coloring m coloring)) in
          loop (eadd child d) cont
        end
  in
    elength (loop (eempty IntInf.compare) coloringltop)
  end



val m44lleafs = map (all_leafs o unzip_mat) m44l;
sum_int m44lleafs;


val m44l = read_par 12 (4,4);
val m35l = read_par 12 (3,5);
val m44l1 = dict_sort compare_imax 
  (map_assoc (number_of_holes o unzip_mat) m44l);

val m35l1 = dict_sort compare_imax 
  (map_assoc (number_of_holes o unzip_mat) m35l);

val m35i = fst (hd m44l1);
val m44i = fst (hd m35l1);

val m44 = unzip_mat m44i;
val m35 = unzip_mat m35i;
number_of_holes m44;
number_of_holes m35;
val (_,t) = add_time (glue false (4,5) m35i) m44i;

fun shift_edgecl x ecl = map (fn ((a,b),c) => ((a + x, b + x),c)) ecl;

fun diag_mat m1 m2 = 
  let
    val ecl1 = mat_to_edgecl m1
    val ecl2 = shift_edgecl (mat_size m1) (mat_to_edgecl m2)
    val m = edgecl_to_mat (mat_size m1 + mat_size m2) (ecl1 @ ecl2)
  in
    m
  end
  
fun diag_mate m1 m2 =
  let
    val size = mat_size m1 + mat_size m2 + 1
    val m1size = mat_size m1
    val m2size = mat_size m2
    val ecl1 = mat_to_edgecl m1
    val ecl2 = shift_edgecl m1size (mat_to_edgecl m2)
    val ecl3 = List.tabulate (m1size, fn i => ((i,size - 1),2))
    val ecl4 = List.tabulate (m2size, fn i => ((i + m1size,size -1),1)) 
    val m = edgecl_to_mat size (ecl1 @ ecl2 @ ecl3 @ ecl4)
  in
    m
  end; 
  
fun smart_neg tm = if is_neg tm then dest_neg tm else mk_neg tm;

fun mk_atmost n xl =
  let val sets = subsets_of_size (n+1) xl in
    map (list_mk_disj o map smart_neg) sets
  end;

fun satvar i j = mk_var ("E_" ^ its i ^ "_" ^ its j,bool);

val ERR = mk_HOL_ERR "test";

fun degree_clauses color graph maxdeg v = 
  let
    val noneighbor = neighbor_of 0 graph v
    val vl = map (fn x => if x < v then satvar x v else satvar v x) noneighbor
    val deg = maxdeg - length (neighbor_of color graph v)
    val _ = if deg <= 0 then raise ERR "degree_clauses" "unexpected" else ()
  in  
    mk_atmost deg vl
  end;
  
val graph = diag_mate m44 m35;
  
val color = blue;
val maxdeg = 12;  
val v = 0;
val x = 
  List.concat (map (degree_clauses color graph maxdeg) (List.tabulate (24,I)));
val y = degree_clauses color graph maxdeg v;
  
  
print_mat (diag_mate m44 m35);  
fun E a b = "E" ^ its a ^ "-" ^ its b
fun X i = "X" ^ its i;
fun S i j = "S" ^ its i ^ "-" ^ its j;
fun F s = (s,false)
fun T s = (s,true)

(* -------------------------------------------------------------------------
   Ramsey clauses
   ------------------------------------------------------------------------- *)

val blue = 1
val red =2

fun clique_of_subset (subset,color) =
  let 
    val pairl = all_pairs (dict_sort Int.compare subset) 
    fun f (a,b) = (E a b, color <> blue)
  in
    map f pairl
  end

fun ramsey_clauses size (bluesize,redsize) = 
  let
    val vertexl = List.tabulate (size,I)
    val bluesubsetl = subsets_of_size bluesize vertexl
    val redsubsetl = subsets_of_size redsize vertexl
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end

(* -------------------------------------------------------------------------
   Degree clauses
   ------------------------------------------------------------------------- *)

fun atmostk1 n = range (1, n-1, fn i => [F (X i), T (S i 1)]);
fun atmostk2 k = range (2,k, fn j => [F (S 1 j)])
fun atmostk3 k n = List.concat (
  range (2,n-1, fn i => range (1,k, fn j => 
    [F (S (i-1) j), T (S i j)])));   
fun atmostk4 k n = List.concat (
  range (2,n-1, fn i => range (2,k, fn j => 
    [F (S (i-1) (j-1)), F (X i), T (S i j)])));
fun atmostk5 k n = 
  range (2,n, fn i => [F (S (i-1) k), F (X i)]);

fun atmostk k n = List.concat 
  [atmostk1 n, atmostk2 k, atmostk3 k n, atmostk4 k n, atmostk5 k n]

fun atleastk k n = 
  let fun f (x,b) = if String.isPrefix "X" x then (x,not b) else (x,b) in
    map (map f) (atmostk (n-k) n)
  end
  
fun atmostk_named k vl sprefix =
  let 
    val n = length vl
    val Xl = List.tabulate (n, fn i => X (i+1));   
    val d = dnew String.compare (combine (Xl,vl))
    fun f x = if String.isPrefix "X" x then dfind x d else sprefix ^ x
  in
    map (map_fst f) (atmostk k n)
  end
  
fun atleastk_named k vl sprefix =
  let 
    val n = length vl
    val Xl = List.tabulate (n, fn i => X (i+1));   
    val d = dnew String.compare (combine (Xl,vl))
    fun f x = if String.isPrefix "X" x then dfind x d else sprefix ^ x
  in
    map (map_fst f) (atleastk k n)
  end

fun edges_of_vertex vertexl v = 
  let 
    fun f w = if v = w then NONE else 
      if v < w then SOME (v,w) else SOME (w,v)
    fun g (a,b) = E a b
  in
    map g (List.mapPartial f vertexl)
  end

fun cdeg size csize (mindeg,maxdeg) =
  let val vertexl = List.tabulate (size,I) in
    List.concat 
    (List.tabulate (csize, fn v =>
    let 
      val edgel = edges_of_vertex vertexl v
      val vl = atleastk_named mindeg edgel ("VL" ^ its v ^ "_")
      val vm = atmostk_named maxdeg edgel ("VM" ^ its v  ^ "_")
    in
      vl @ vm
    end))
  end

fun ddeg size csize (mindeg,maxdeg) = 
  let val vertexl = List.tabulate (size,I) in
    List.concat 
    (range (csize,size-1, fn v =>
    let 
      val edgel = edges_of_vertex vertexl v
      val vl = atleastk_named mindeg edgel ("VL" ^ its v ^ "_")
      val vm = atmostk_named maxdeg edgel ("VM" ^ its v  ^ "_")
    in
      vl @ vm
    end)) 
  end

fun E a b = "E" ^ its a ^ "-" ^ its b
fun X i = "X" ^ its i;
fun S i j = "S" ^ its i ^ "-" ^ its j;
fun F s = (s,false)
fun T s = (s,true)

(* -------------------------------------------------------------------------
   Ramsey clauses
   ------------------------------------------------------------------------- *)

fun clique_of_subset (subset,color) =
  let 
    val pairl = all_pairs (dict_sort Int.compare subset) 
    fun f (a,b) = (E a b, color <> blue)
  in
    map f pairl
  end

fun ramsey_clauses size (bluesize,redsize) = 
  let
    val vertexl = List.tabulate (size,I)
    val bluesubsetl = subsets_of_size bluesize vertexl
    val redsubsetl = subsets_of_size redsize vertexl
    val subsetl = map_assoc (fn _ => blue) bluesubsetl @
                  map_assoc (fn _ => red) redsubsetl
  in
    map clique_of_subset subsetl
  end
*)
