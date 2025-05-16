structure graph :> graph =
struct   

open HolKernel Abbrev boolLib aiLib kernel smlParallel
val ERR = mk_HOL_ERR "graph"

type vertex = int
type edge = int * int
type color = int
type mat = color Array2.array
type coloring = (edge * color) list

val blue = 1
val red =2

(* -------------------------------------------------------------------------
   Array2 shortcuts
   ------------------------------------------------------------------------- *)

fun mat_sub (m,i,j) = Array2.sub (m,i,j)
fun mat_update (m,i,j,x) = Array2.update(m,i,j,x)
fun mat_update_sym (m,i,j,x) = 
  (mat_update (m,i,j,x); mat_update (m,j,i,x))

fun mat_empty n = Array2.array (n,n,0);

fun mat_tabulate (n,f) = Array2.tabulate Array2.RowMajor (n,n,f)
 
fun mat_traverse f m = 
  let 
    val range = {base=m,row=0,col=0,nrows=NONE,ncols=NONE}
    fun g (i,j,x) = if i < j then f (i,j,x) else ()
  in
    Array2.appi Array2.RowMajor g range
  end 

fun mat_size m = 
  let val (a,b) = Array2.dimensions m in
    if a = b then a else raise ERR "mat_size" ""
  end
  
fun mat_copy graph = 
  let fun f (i,j) = mat_sub (graph,i,j) in
    mat_tabulate (mat_size graph, f)
  end  

(* -------------------------------------------------------------------------
   Helpers for undirected graphs
   ------------------------------------------------------------------------- *)
  
fun symmetrify m = 
  mat_tabulate (mat_size m, fn (a,b) => 
  if a=b then 0 else if a < b then mat_sub (m,a,b) else mat_sub (m,b,a));  
  
(* -------------------------------------------------------------------------
   Comparison functions
   ------------------------------------------------------------------------- *)

val edge_compare = cpl_compare Int.compare Int.compare  

val edgec_compare = 
  cpl_compare (cpl_compare Int.compare Int.compare) Int.compare

fun mat_compare_aux size a1 a2 i j = 
  case Int.compare (mat_sub (a1,i,j),mat_sub (a2,i,j)) of
      EQUAL => if j >= size - 1 then 
                 if i >= size - 1 
                 then EQUAL 
                 else mat_compare_aux size a1 a2 (i+1) 0
               else mat_compare_aux size a1 a2 i (j+1)
    | r => r;


fun mat_compare (a1,a2) = 
  case Int.compare (mat_size a1, mat_size a2) of
    EQUAL => mat_compare_aux (mat_size a1) a1 a2 0 0
  | x => x 

fun mat_eq a1 a2 = mat_compare (a1,a2) = EQUAL

(* same as mat_compare but faster if the size are equal *)
fun mat_compare_fixedsize size (a1,a2) = mat_compare_aux size a1 a2 0 0  
    
val mat_set = mk_fast_set mat_compare

(* -------------------------------------------------------------------------
   Initialization
   ------------------------------------------------------------------------- *)

fun random_mat size = symmetrify
  (mat_tabulate (size,fn (a,b) => if a=b then 0 else random_int (0,2)));

fun random_full_mat size = symmetrify
  (mat_tabulate (size,fn (a,b) => if a=b then 0 else random_int (1,2)));

fun matK size = 
  mat_tabulate (size,fn (a,b) => if a=b then 0 else 1);
 
fun matKn size n = 
  mat_tabulate (size + 1, fn (a,b) => 
    if (a = size andalso b >= n) orelse 
       (b = size andalso a >= n) orelse (a=b) 
    then 0 else 1);

(* -------------------------------------------------------------------------
   Neighbors
   ------------------------------------------------------------------------- *)

fun neighbor_of color graph x = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = mat_sub (graph,x,y) = color
  in
    filter test vertexl
  end
  handle Subscript => raise ERR "neighbor_of" ""
  
fun commonneighbor_of color graph (a,b) = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = (mat_sub (graph,a,y) = color andalso 
                  mat_sub (graph,b,y) = color)
  in
    filter test vertexl
  end
  handle Subscript => raise ERR "commonneighbor_of" ""  


fun all_neighbor color graph = 
  List.tabulate (mat_size graph, neighbor_of color graph) 

fun inneighbor_of color graph x = 
  let 
    val vertexl = List.tabulate (mat_size graph,I)
    fun test y = mat_sub (graph,y,x) = color
  in
    filter test vertexl
  end

(* -------------------------------------------------------------------------
   Debug
   ------------------------------------------------------------------------- *)

fun string_of_edge (i,j) = its i ^ "-" ^ its j
fun edge_of_string s = pair_of_list (map string_to_int 
  (String.tokens (fn x => x = #"-") s))

fun string_of_edgel edgel = String.concatWith " " (map string_of_edge edgel)
fun edgel_of_string s = map edge_of_string (String.tokens Char.isSpace s)

fun string_of_edgec ((i,j),x) = its i ^ "-" ^ its j ^ ":" ^ its x
fun edgec_of_string s = 
  let 
    val (s1,s2) = split_pair #":" s
    val (s1a,s1b) = split_pair #"-" s1
  in
    ((string_to_int s1a, string_to_int s1b), string_to_int s2)
  end
  
fun string_of_edgecl edgecl = String.concatWith " " (map string_of_edgec edgecl)
fun edgecl_of_string s = map edgec_of_string (String.tokens Char.isSpace s)

fun named_neighbor color graph = 
  let
    val l1 = number_fst 0 (all_neighbor color graph) 
    fun g (i,l) = (i, filter (fn x => x > i) l)
    val l2 = map g l1
  in
    filter (not o null o snd) l2
  end

fun string_of_graph graph = 
  let fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) in
    String.concatWith " " (map f (named_neighbor blue graph)) ^ " | " ^
    String.concatWith " " (map f (named_neighbor red graph))
  end

fun string_of_bluegraph graph = 
  let fun f (i,l) = its i ^ "-" ^ String.concatWith "_" (map its l) in
    String.concatWith ", " (map f (named_neighbor blue graph))
  end
  
fun mat_to_ll m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => mat_sub (m,i,j)))
  end

fun string_of_mat m = String.concatWith "\n" (map ilts (mat_to_ll m))

fun print_mat m = print_endline (string_of_mat m); 
  
fun mat_to_ll_nodiag m = 
  let val size = mat_size m in
    List.tabulate (size, fn i => List.tabulate (size,fn j => 
      if i = j then ~1 else mat_sub (m,i,j)))
  end

fun mat_to_latex m =
  let
    val size = mat_size m
    val linel = mat_to_ll_nodiag m
    fun f c = if c = ~1 then "\\#"
              else if c = 0 then "\\*" 
              else if c = 1 then "o" 
              else if c = 2 then "-" 
              else raise ERR "mat_to_latex" ""
    fun fline line = String.concatWith "," (map f line)
  in
    map fline linel 
  end
  
fun write_latexmat file m = writel file (mat_to_latex m)
   

(* -------------------------------------------------------------------------
   Switching between representations
   todo: store the size at the beginning of a edgecl for easier reconstruction
   ------------------------------------------------------------------------- *)

fun mat_to_edgecl m =
  let 
    val l = ref []
    fun f (i,j,x) = if x <> 0 then l := ((i,j),x) :: !l else ()      
  in
    mat_traverse f m; rev (!l)
  end  

fun edgecl_to_mat size edgecl =
  let 
    val edgel = map fst edgecl
    val edged = dnew (cpl_compare Int.compare Int.compare) edgecl
    fun f (i,j) = case dfindo (i,j) edged of NONE => 0 | SOME c => c 
  in
    symmetrify (mat_tabulate (size, f))
  end

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

(* -------------------------------------------------------------------------
   Graph I/O
   ------------------------------------------------------------------------- *)

fun find_size i ln = 
  if i > 10000 then raise ERR "find_size" "size > 10000" else
  if i * (i-1) div 2 = ln then i else find_size (i+1) ln

local open IntInf in

fun zip_mat m = 
  let 
    val r = ref 1
    fun f (i,j,x) = if r > 3 orelse r < 0 
                    then raise ERR "zip_mat" "entries must be 0,1 or 2" 
                    else r := !r * 3 + IntInf.fromInt x
  in
    mat_traverse f m; !r
  end

fun all_edges size =
  let 
    val m = mat_tabulate (size, fn _ => 0)
    val r = ref []
    fun f (i,j,x) = r := (i,j) :: !r
  in
    mat_traverse f m;
    rev (!r)
  end    

fun unzip_mat mati =
  let 
    fun loop x = if x < 3 then [] else x mod 3 :: loop (x div 3) 
    val l1 = rev (loop mati)
    val size = find_size 1 (length l1)
    val l2 = all_edges size
    val edgecl = combine (l2, map IntInf.toInt l1)
  in
    edgecl_to_mat size edgecl
  end      
  
end (* local *)

fun szip_mat m = IntInf.toString (zip_mat m)
fun sunzip_mat s = unzip_mat (valOf (IntInf.fromString s))


val base64chars = Vector.fromList (
  List.tabulate (26, fn i => Char.chr (i + Char.ord #"A")) @
  List.tabulate (26, fn i => Char.chr (i + Char.ord #"a")) @
  List.tabulate (10, fn i => Char.chr (i + Char.ord #"0")) @
  [#"-", #"_"])

local open IntInf in

fun base10to64rev i = 
  if i < 0 then raise ERR "base10to64rev" "negative" 
  else if i < 64 then [IntInf.toInt i] 
  else IntInf.toInt (i mod 64) :: base10to64rev (i div 64) 

end

fun name_mat m = 
  let val l = rev (base10to64rev (zip_mat m)) in 
    implode (map (fn x => Vector.sub (base64chars,x)) l)
  end


local open IntInf in

fun zip_full m =
  let 
    val r = ref 1 
    fun f (i,j,x) = r := !r * 2 + (if x = blue then 1 else 0) 
  in
    mat_traverse f m; !r
  end

fun unzip_full size mati =
  let 
    fun loop x = if x < 2 then [] else x mod 2 :: loop (x div 2) 
    val l1 = rev (loop mati)
    val l2 = all_edges size
    val edgecl0 = combine (l2, map IntInf.toInt l1)
    val edgecl1 = map_snd (fn b => if b = 1 then blue else red) edgecl0
  in
    edgecl_to_mat size edgecl1
  end
  
fun unzip_full_edgecl size mati =
  let 
    fun loop x = if x < 2 then [] else x mod 2 :: loop (x div 2) 
    val l1 = rev (loop mati)
    val l2 = all_edges size
    val edgecl0 = combine (l2, map IntInf.toInt l1)
    val edgecl1 = map_snd (fn b => if b = 1 then blue else red) edgecl0
  in
    edgecl1
  end  
  
end (* local *)

(* 
PolyML.print_depth 0;
load "ramsey"; open aiLib kernel ramsey;
PolyML.print_depth 20;
val m = random_full_symmat 11;
val i = zip_full m;
val m1 = unzip_full 11 i;
mat_compare (m,m1);
*)

(* -------------------------------------------------------------------------
   Permutations
   ------------------------------------------------------------------------- *)

fun extend_mat m n = edgecl_to_mat (mat_size m + 2) (mat_to_edgecl m)

fun mat_permute (m,size) sigma =
  let fun f (x,y) = mat_sub (m, sigma x, sigma y) in
    mat_tabulate (size, f)
  end
 
fun insert_everywhere elem l = case l of 
    [] => [[elem]]
  | a :: m => (elem :: a :: m) :: 
    map (fn m' => a::m') (insert_everywhere elem m);

fun permutations l = case l of 
    [] => [[]] 
  | a :: m => List.concat (map (insert_everywhere a) (permutations m));

fun mk_permf perm = 
  let 
    val permv = Vector.fromList perm
    fun f n = Vector.sub (permv,n) 
  in 
    f 
  end

fun neighborm_of color m v =
  let val vl = neighbor_of color m v in
    mat_permute (m,length vl) (mk_permf vl)
  end

(* only works for full perm *)
fun invert_perm perm = 
  let val permd = dnew Int.compare (number_snd 0 perm) in
    List.tabulate (dlength permd, fn i => dfind i permd)
  end 
  
fun random_subgraph subsize m =
  let
    val vertexl = List.tabulate (mat_size m,I)
    val perm = random_elem (subsets_of_size subsize vertexl)
    val permf = mk_permf perm
  in
    mat_permute (m,subsize) permf
  end


exception Merge;
fun mat_merge m1 m2 = 
  let 
    val _ = if mat_size m1 <> mat_size m2 then raise ERR "mat_merge" "" else ()
    fun f (i,j) = 
      let val (a,b) = (mat_sub (m1,i,j),mat_sub (m2,i,j)) in
        if a = 0 andalso b = 0 then 0
        else if a = 0 then b
        else if b = 0 then a
        else if a = b then a else raise Merge
      end
  in
    SOME (mat_tabulate (mat_size m1,f)) handle Merge => NONE
  end;

fun mat_inject size m vl = 
  let 
    val d = dnew Int.compare (number_snd 0 vl);
    fun f (i,j) = mat_sub (m,dfind i d, dfind j d) handle NotFound => 0
  in
    mat_tabulate (size,f)
  end

(* -------------------------------------------------------------------------
   Generalizations and colorings
   ------------------------------------------------------------------------- *)

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
  
fun swap_colors m = 
  let fun f (i,j) = 
    let val x = mat_sub (m,i,j) in if x = 0 then 0 else 3-x end
  in 
    mat_tabulate (mat_size m, f)
  end

(* -------------------------------------------------------------------------
   Properties
   ------------------------------------------------------------------------- *)

fun number_of_edges m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x <> 0 then incr y else ()
  in
    mat_traverse f m; 
    !y
  end

fun number_of_blueedges m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x = 1 then incr y else ()
  in
    mat_traverse f m; 
    !y
  end  

fun number_of_holes m = 
  let 
    val y = ref 0 
    fun f (i,j,x) = if x = 0 then incr y else ()
  in
    mat_traverse f m;  !y
  end

fun all_holes m = 
  let 
    val l = ref [] 
    fun f (i,j,x) = if x = 0 then l := (i,j) :: !l else ()
  in
    mat_traverse f m; !l
  end
  
fun all_cedges m = 
  let 
    val l = ref [] 
    fun f (i,j,x) = if x <> 0 then l := (i,j) :: !l else ()
  in
    mat_traverse f m; !l
  end 

fun is_clique m color l = 
  let val l' = map pair_of_list (subsets_of_size 2 l) in
    all (fn (a,b) => mat_sub (m,a,b) = color) l'
  end

fun all_cliques size color m =
  let 
    val vl = List.tabulate (mat_size m,I) 
    val cliquel = subsets_of_size size vl
  in
    filter (is_clique m color) cliquel
  end
  
(* works with holes *)
fun is_ramsey (bluen,redn) topm = 
  let 
    val vertexl = List.tabulate (mat_size topm,I)
    val bluem = mat_copy topm 
    fun f (i,j,x) = if x = 0 then mat_update_sym (bluem,i,j,blue) else ()
    val _ = mat_traverse f topm
    val redm = mat_copy topm
    fun f (i,j,x) = if x = 0 then mat_update_sym (redm,i,j,red) else ()
    val _ = mat_traverse f topm
    fun is_clique m color l = 
      let val l' = map pair_of_list (subsets_of_size 2 l) in
        all (fn (a,b) => mat_sub (m,a,b) = color) l'
      end
  in
    not (exists (is_clique bluem blue) (subsets_of_size bluen vertexl)) andalso
    not (exists (is_clique redm red) (subsets_of_size redn vertexl)) 
  end


fun subsets1_f f x1 x2 x3 x4 l = case l of 
    [] => ()
  | x5 :: m5 => (f x1 x2 x3 x4 x5; subsets1_f f x1 x2 x3 x4 m5);
                                             
fun subsets2_f f x1 x2 x3 l = case l of 
    [] => ()
  | x4 :: m4 => (subsets1_f f x1 x2 x3 x4 m4; subsets2_f f x1 x2 x3 m4)

fun subsets3_f f x1 x2 l = case l of 
    [] => ()
  | x3 :: m3 => (subsets2_f f x1 x2 x3 m3; subsets3_f f x1 x2 m3);
  
fun subsets4_f f x1 l = case l of 
    [] => ()
  | x2 :: m2 => (subsets3_f f x1 x2 m2; subsets4_f f x1 m2);

fun subsets5_f f l = case l of 
    [] => ()
  | x1 :: m1 => (subsets4_f f x1 m1; subsets5_f f m1);

fun forall_pairs f (a,b,c,d,e) = 
  f (a,b) andalso f (a,c) andalso f (a,d) andalso f (a,e) andalso
  f (b,c) andalso f (b,d) andalso f (b,e) andalso
  f (c,d) andalso f (c,e) andalso
  f (d,e);
  
  
fun is_good_lit color mat (i,j) =
  let val newcolor = mat_sub (mat,i,j) in
    newcolor = 0 orelse color = newcolor
  end;
 
fun all_5cliques color m = 
  let 
    val l = ref []
    val vertexl = List.tabulate (mat_size m,I)
    fun f a b c d e = 
      if forall_pairs (is_good_lit color m) (a,b,c,d,e) 
      then l := (a,b,c,d,e) :: !l
      else ()
  in 
    subsets5_f f vertexl; !l
  end

(* -------------------------------------------------------------------------
   Cliques
   ------------------------------------------------------------------------- *)

fun exist_withtail f l = case l of 
    [] => false
  | a :: m => f a m orelse exist_withtail f m

fun exist_clique_v n f v l =
  exist_clique (n-1) f (filter (fn x => f(v,x)) l)
  
and exist_clique n f l = 
  if n = 0 then true else
  if length l < n then false else
  exist_withtail (exist_clique_v n f) l

fun exist_clique_mat m (color,size) =
  let 
    fun f (i,j) = let val newcolor = mat_sub (m,i,j) in
                    newcolor = color
                  end
    val vl = List.tabulate (mat_size m,I)
  in
    exist_clique size f vl
  end

fun exist_clique_edge m (color,size) (a,b) =
  let 
    fun f (i,j) = let val newcolor = mat_sub (m,i,j) in
                    newcolor = color
                  end              
    val vl = List.tabulate (mat_size m,I)
    val vl' = filter (fn x => f(a,x) andalso f(b,x)) vl
  in
    exist_clique (size-2) f vl'
  end

fun can_extend_edge (bsize,rsize) m (a,b) =
  let 
    val orgcolor = mat_sub (m,a,b) 
    val color = 3-orgcolor
    val size = if color = blue then bsize else rsize
  in
    exist_clique_edge m (color,size) (a,b)
  end

(* -------------------------------------------------------------------------
   List all cliques of size n
   ------------------------------------------------------------------------- *)

fun all_withtail f l = case l of 
    [] => []
  | a :: m => (f a m @ all_withtail f m)

fun all_clique_v n f v l =
  map (fn x => v :: x) (all_clique (n-1) f (filter (fn x => f(v,x)) l))

and all_clique n f l = 
  if n = 0 then [[]] else
  if length l < n then [] else
  all_withtail (all_clique_v n f) l
;  

fun all_clique_mat m (color,size) =
  let 
    fun f (i,j) = let val newcolor = mat_sub (m,i,j) in
                    newcolor = color orelse newcolor = 0
                  end
    val vl = List.tabulate (mat_size m,I)
  in
    all_clique size f vl
  end

end (* struct *)
