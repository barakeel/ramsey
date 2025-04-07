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

(* sometimes completion does not complete fully *)
val other_clausel = ref []

fun complete_graph (bsize,rsize) m = 
  let
    val file = selfdir ^ "/aaa_complete"
    val clausel = ramsey_clauses_mat (bsize,rsize) m @ !other_clausel
    val _ = write_dimacs file clausel
    val cmd = "cadical -q " ^ file ^ " > " ^ file ^ "_sol"
    val (_,t) = add_time (cmd_in_dir selfdir) cmd
  in
    case read_sol file of
      NONE => NONE
    | SOME sol => SOME (edgecl_to_mat (mat_size m) (sol @ mat_to_edgecl m))
  end;



(* 
load "satio"; load "enum"; load "nauty"; load "gen";
open aiLib kernel graph enum glue satio nauty gen;

val csize = 10;
val m1 = random_elem (enum.read_enum csize (3,5));
val m2 = random_elem (enum.read_enum (21 - csize) (4,4));
val mdiag = diag_mat (unzip_mat m1) (unzip_mat m2);

(* todo prefer conflicts that would result in a small clause *)

(* enumerating 4,5 *)
fun new_clause clausel =
  let
    val _ = other_clausel := clausel
    val _ = print_endline "completion"
  in
    case (complete_graph (4,5) mdiag) of NONE => NONE | SOME mfull =>
    let
      val edgecgenl = list_diff (mat_to_edgecl mfull) (mat_to_edgecl mdiag);
      val _ = extra_clausel := clausel
      val _ = print_endline "generalization"
      val edgel = dict_sort edge_compare
        (gen_simple (4,5) edgecgenl 1000 (zip_mat mfull) 1);
      val _ = print_endline ("edgel: " ^ string_of_edgel edgel)
      val d = enew edge_compare edgel;
      val clause = filter (fn (a,b) => not (emem a d)) edgecgenl
    in
      SOME (dict_sort (fst_compare edge_compare) clause)
    end
 end;

val clause1 = new_clause [];
val clause2 = new_clause [clause1];
val clause3 = new_clause [clause1,clause2];

fun loop clausel = 
  let 
    val (newclauseo,t) = add_time new_clause clausel 
    val _ = print_endline (its (length clausel) ^ ": " ^ rts_round 2 t)
  in
    case newclauseo of 
      NONE => clausel
    | SOME newclause => loop (newclause :: clausel)
  end;

val clausel = loop [];


val edgel1 = available_gen (4,5) edgecgenl (zip_mat mfull);
val edgel1' = edge_sort edgel1;

val edgel2' = edgel2;

val edgel3 = edge_sort (gen_simple (4,5) edgecgenl nhole (zip_mat mfull) 1);


list_compare edge_compare (edgel2',edgel3);
list_diff edgel2' edgel3;
list_diff edgel3 edgel2';

val edgell = List.tabulate (10, fn _ =>  
  gen_simple (4,5) edgecgenl nhole (zip_mat mfull) 1);

val m55 = diag_mat mfull (swap_colors mfull);

val extral = List.tabulate (21, fn x => x + 21);

  
val m55' = mat_copy m55;  

fun loop () =
  let
    val (bnl',rnl') = part_n (random_int (0,21)) (shuffle extral);
    val bnl = neighbor_of 1 m55 0 @ bnl';
    val rnl = neighbor_of 2 m55 0 @ rnl';
    val bm = mat_permute (m55,length bnl) (mk_permf bnl);
    val rm = mat_permute (m55,length rnl) (mk_permf rnl);
    val bmfull = complete_graph (4,5) bm;
  in
    if not (isSome bmfull) then loop () else
    let
      val _ = print "."
      val rmfull = complete_graph (5,4) rm
    in
      if not (isSome rmfull) then loop () else
      (bnl,rnl,valOf bmfull,valOf rmfull)
    end
  end;

val (r,t) = add_time loop ();
val (bperm,rperm,bm,rm) = r;

val bd = dnew Int.compare (number_snd 0 bperm);
val bmincl = mat_tabulate (42, fn (i,j) => mat_sub (bm,dfind i bd, dfind j bd) handle NotFound => 0);

val rd = dnew Int.compare (number_snd 0 rperm);
val rmincl = mat_tabulate (42, fn (i,j) => mat_sub (rm,dfind i rd, dfind j rd) handle NotFound => 0);

val ERR = mk_HOL_ERR "test";
fun merge_mat size m1 m2 = 
  let 
    fun f (i,j) = 
      let val (a,b) = (mat_sub (m1,i,j),mat_sub (m2,i,j)) in
        if a = 0 andalso b = 0 then 0
        else if a = 0 then b
        else if b = 0 then a
        else if a = b then a else raise ERR "merge_mat" ""
      end
  in
    mat_tabulate (size,f)
  end;
  
val rbmincl = merge_mat 42 bmincl rmincl;  

val m55incl = merge_mat 42 m55 rbmincl;

val neigh = mat_tabulate (42, fn (i,j) => 
  if i = 0 andalso dmem j bd then 1
  else if i = 0 andalso dmem j rd then 2
  else 0);
  
val m55incl2 = merge_mat 42 m55incl neigh;  

val (x,t) = add_time (complete_graph (5,5)) m55incl;
val (x,t) = add_time (complete_graph (5,5)) m55incl2;

(* todo generalization with binary clauses *)

blue blue
red blue
red red

3/4 better generalization
2/4 

but equality do not make sense if one can just generalize
one of them

(* let's try distinct support for now *)
(* the generalization must work for all edgecll *)

Do the process in the most stupid way.

Have a tester for Ramsey (4,5) maybe with edges

Delete a color
Add a color
And split a

it's possible to have a conflict with the predecessor and
not put them as clauses (or one can put them as clauses).

fun gen_bin mi edgecll = 
  
  



Test the idea: on 4,5 first if it is good it should be
speeding up 4,5. Evaluate the idea of double splitting.
maybe a concept of distance to keep only the ones that are close
*)


end (* struct *)
