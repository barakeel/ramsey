(* =========================================================================
   Compute a set of generalized graphs covering a set of graph
   uset stands for uncovered set.
   ========================================================================= *)
   
structure gen :> gen =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty syntax enum
val ERR = mk_HOL_ERR "gen"
type vleafs = int * int * (IntInf.int * int list) list  

val nauty_time = ref 0.0
val normalize_nauty = total_time nauty_time normalize_nauty

(* -------------------------------------------------------------------------
   Getting all_leafs of 
   ------------------------------------------------------------------------- *) 

fun all_leafs_wperm_aux (iall,inew) uset m =
  let
    val edgel = all_holes m
    val coloringltop = all_coloring edgel
    val d = ref (dempty IntInf.compare)
    fun loop d e coloringl = case coloringl of 
        [] => (!iall,!inew,d,e)
      | coloring :: cont =>
        let 
          val child = apply_coloring m coloring     
          val (normm,perm) = normalize_nauty_wperm child
          val normi = zip_mat normm
          val newe = eadd normi e
          val _ = incr iall
        in
          if emem normi uset
          then (incr inew; loop (dadd normi perm d) newe cont)   
          else loop d newe cont
        end
  in
    loop (dempty IntInf.compare) (eempty IntInf.compare) coloringltop 
  end

fun all_leafs_wperm uset m = all_leafs_wperm_aux (ref 0, ref 0) uset m

(* -------------------------------------------------------------------------
   Scoring generalizations: lower number is better.
   ------------------------------------------------------------------------- *)

val clique35 = [(1,1),(2,1),(2,2),(3,2),(4,2)]
val clique44 = [(3,1),(2,1),(3,2),(2,2),(1,2)]

fun number_of_cliques m (n,color) =
  let 
    val vl = List.tabulate (mat_size m, I)
    val cliquel = subsets_of_size n vl
    fun is_uniform x = 
      let 
        val edgel = all_pairs x 
        fun test (i,j) = mat_sub (m,i,j) = color 
      in
        all test edgel
      end
  in
    ((n,color), Real.fromInt (length (filter is_uniform cliquel)))
  end

fun get_stats35 m = map (number_of_cliques m) clique35
fun get_stats44 m = map (number_of_cliques m) clique44

fun get_average35 enum =
  let val l = map (map snd o get_stats35 o unzip_mat) enum in
    combine (clique35, map average_real (list_combine l))
  end

fun get_average44 enum =
  let val l = map (map snd o get_stats44 o unzip_mat) enum in
    combine (clique44, map average_real (list_combine l))
  end

(*
load "gen"; open enum gen;
val enum3510 = read_enum 10 (3,5);
val enum4414 = read_enum 14 (4,4);

*)


fun difficulty stats35 stats45 =
  let 
    val l = combine (stats35,stats45)
    fun f (((n1,_),r1),((n2,_),r2)) = 
      r1 * r2 * (1.0 / Math.pow (2.0, Real.fromInt (n1 * n2)))
  in
    sum_real (map f l)
  end

fun init_scored size (bluen,redn) =
  if (bluen,redn) = (3,5) then
    let 
      val enum35 = read_enum size (3,5)
      val enum44 = read_enum (24-size) (4,4)
      val average44 = get_average44 enum44
      fun score35 x = difficulty (get_stats35 (unzip_mat x)) average44
    in
      dnew IntInf.compare (map_assoc score35 enum35)
    end
  else if (bluen,redn) = (4,4) then
    let 
      val enum35 = read_enum (24-size) (3,5)
      val enum44 = read_enum size (4,4)
      val average35 = get_average35 enum35
      fun score44 x = difficulty average35 (get_stats44 (unzip_mat x))
    in
      dnew IntInf.compare (map_assoc score44 enum44)
    end
  else raise ERR "init_scored" "unexpected"
  
(* -------------------------------------------------------------------------
   Cover
   ------------------------------------------------------------------------- *)

fun enc_color (x,c) = if c = 1 then 2 * x else 2 * x + 1;
fun enc_edgec (e,c) = enc_color (edge_to_var e,c);
fun dec_edgec x = (var_to_edge (x div 2), (x mod 2) + 1);
fun opposite (e,x) = (e,3 - x)

fun init_sgen size (bluen,redn) = 
  let
    val clauses1 = sat.ramsey_clauses size (bluen,redn)
    val clauses2 = map (map enc_color) clauses1
    val clausev = Vector.fromList clauses2;
    val claused = dnew (list_compare Int.compare) (number_snd 0 clauses2)
    fun g clause = map_assoc (fn _ => clause) clause
    val clauses3 = List.concat (map g clauses2)
    val clauses4 = dlist (dregroup Int.compare clauses3)
    val clauses5 = map_snd (map (fn x => dfind x claused)) clauses4
    val clauses6 = map_snd (dict_sort Int.compare) clauses5
    val varv = Vector.fromList (map snd clauses6)
  in
    (varv,clausev)
  end;
  
fun build_parent leaf edgel = 
  let
    val parent = mat_copy leaf
    fun f (i,j) = mat_update_sym (parent,i,j,0)
    val _ = app f edgel
  in
    parent
  end;     
  
fun build_sibling leaf edgel (itop,jtop) = 
  let
    val sibling = build_parent leaf edgel
    val oppc = 3 - mat_sub (leaf,itop,jtop)
    val _ = mat_update_sym (sibling,itop,jtop,oppc)
  in
    sibling
  end

fun concat_cpermll (leafi,vleafsl) = 
  let val idperm = List.tabulate (mat_size (unzip_mat leafi),I) in
    mk_fast_set (fst_compare IntInf.compare)
      ((leafi,idperm) :: List.concat (map #3 vleafsl))
  end

fun sgen maxhole_loc (bluen,redn) leafi =
  let
    val leaf = unzip_mat leafi
    val size = mat_size leaf
    val (varv,clausev) = init_sgen size (bluen,redn) 
    val sizev = Vector.map (fn x => length x - 1) clausev
    val inita = Array.array (Vector.length clausev,0)    
    fun update_numbera a v = 
      let 
        val il = Vector.sub (varv,v) 
        fun g i = Array.update (a,i, Array.sub(a,i) + 1) 
      in
        app g il
      end
    val edgecl = mat_to_edgecl leaf
    val _ = app (update_numbera inita) (map enc_edgec edgecl)
    fun try () = 
      let
        val locala = Array.tabulate 
          (Array.length inita, fn i => Array.sub (inita,i))
        val vlopp = shuffle (map (enc_edgec o opposite) edgecl)
        fun test v = 
          let val clausel = Vector.sub (varv,v) in
            all (fn x => Array.sub (locala, x) < Vector.sub(sizev,x)) clausel
          end
        fun sgen_loop vl result = 
          if length result >= maxhole_loc then rev result else
          case vl of
            [] => rev result
          | v :: rem => (update_numbera locala v;
                         sgen_loop (filter test rem) 
                           (fst (dec_edgec v) :: result))
      in
        sgen_loop (filter test vlopp) []
      end 
  in  
    try ()
  end;



fun sgeneralize (bluen,redn) uset leafi =
  let
    val leaf = unzip_mat leafi
    val size = mat_size leaf
    val (varv,clausev) = init_sgen size (bluen,redn) 
    val sizev = Vector.map (fn x => length x - 1) clausev
    val inita = Array.array (Vector.length clausev,0)    
    fun update_numbera a v = 
      let 
        val il = Vector.sub (varv,v) 
        fun g i = Array.update (a,i, Array.sub(a,i) + 1) 
      in
        app g il
      end
    val edgecl = mat_to_edgecl leaf
    val _ = app (update_numbera inita) (map enc_edgec edgecl)
    fun try () = 
      let
        val locala = Array.tabulate 
          (Array.length inita, fn i => Array.sub (inita,i))
        val vlopp = shuffle (map (enc_edgec o opposite) edgecl)
        fun test v = 
          let val clausel = Vector.sub (varv,v) in
            all (fn x => Array.sub (locala, x) < Vector.sub(sizev,x)) clausel
          end
        fun sgen_loop vl result = 
          if length result >= maxhole then rev result else
          case vl of
            [] => rev result
          | v :: rem => 
            let 
              val edgel = map (fst o dec_edgec o #1) result
              val edge = fst (dec_edgec v)
              val sibling = build_sibling leaf edgel edge
              val (iall,inew,d,e) = all_leafs_wperm uset sibling
              val maxn = elength e
            in
              if mincover * inew >= iall
              then (update_numbera locala v;
                    sgen_loop (filter test rem) ((v,maxn,dlist d) :: result)) 
              else sgen_loop rem result
            end   
      in
        sgen_loop (filter test vlopp) []
      end 
  in  
    try ()
  end;

(* -------------------------------------------------------------------------
   Finding generalizations not overlapping too much
   ------------------------------------------------------------------------- *)
   
fun sgen_worker ((bluen,redn),uset) leafi =
  let
    val vleafsl = sgeneralize (bluen,redn) uset leafi in
    (leafi, vleafsl)
  end

fun write_infset file ((a,b),set) = writel file 
  (its a :: its b :: map infts (elist set))
fun read_infset file = case readl file of
  sa :: sb :: m => ((string_to_int sa,string_to_int sb), 
                    enew IntInf.compare (map stinf m))
  | _ => raise ERR "read_infset" ""
 
fun write_inf file i = writel file [infts i]
fun read_inf file = stinf (singleton_of_list (readl file))

fun string_of_cperm (c,perm) = 
  String.concatWith "_" (infts c :: map its perm)

fun cperm_of_string s = case String.tokens (fn x => x = #"_") s of
    a :: m => (stinf a, map string_to_int m)
  | _ => raise ERR "cperm_of_string" ""

fun string_of_vleafs (v,maxn,cperml) = 
  String.concatWith " " (its v :: its maxn :: map string_of_cperm cperml)

fun vleafs_of_string s = case String.tokens Char.isSpace s of
    a :: b :: m => (string_to_int a, string_to_int b, map cperm_of_string m)
  | _ => raise ERR "vleafs_of_string" ""

fun write_result file (leafi,vleafsl)  =
  writel file (infts leafi :: map string_of_vleafs vleafsl)

fun read_result file = case readl file of 
    a :: m => (stinf a, map vleafs_of_string m)
  | _ => raise ERR "read_result" ""

val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
  IntInf.int * vleafs list) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "gen.genspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    ["smlExecScripts.buildheap_dir := " ^ mlquote 
      (!smlExecScripts.buildheap_dir)] 
    ^ ")"),
  function = sgen_worker,
  write_param = write_infset,
  read_param = read_infset,
  write_arg = write_inf,
  read_arg = read_inf,
  write_result = write_result,
  read_result = read_result
  }

fun remove_vleafsl_aux uset (leafi,vleafsl) acc = case vleafsl of
    [] => SOME (leafi, rev acc)
  | (v,maxn,cperml) :: m =>  
    let val newcperml = filter (fn x => emem (fst x) uset) cperml in
      if mincover * length newcperml > maxn 
      then remove_vleafsl_aux uset (leafi,m) ((v,maxn,newcperml) :: acc)
      else NONE
    end

fun remove_vleafsl uset (leafi,vleafsl) = 
  if not (emem leafi uset) 
  then NONE 
  else remove_vleafsl_aux uset (leafi,vleafsl) []

val select_number1 = ref 240
val select_number2 = ref 120

fun size_of_vleafsl (vleafsl: vleafs list) = 
  elength (enew IntInf.compare (List.concat (map (map fst o #3) vleafsl)))

fun update_uset selectn pl (uset,result) =
  if elength uset <= 0 orelse 
     null pl orelse 
     selectn >= !select_number2 
     then (uset,result) else
  let 
    val l1 = map_assoc (size_of_vleafsl o snd) pl
    val l2 = dict_sort compare_imax l1
    val (leafi,vleafsl) = fst (hd l2) 
    val cperml = concat_cpermll (leafi,vleafsl)
    val keyl = map fst cperml
    val newuset = ereml keyl uset
    val edgel = map (fst o dec_edgec o #1) vleafsl
    val pari = zip_mat (build_parent (unzip_mat leafi) edgel)
    val newresult = (pari,cperml) :: result
    val newpl = List.mapPartial (remove_vleafsl newuset) pl
    val _ = log ("Covering " ^ its (length cperml) ^ " graphs (" ^ 
                 its (elength newuset) ^ " remaining)" ^
                 " at depth " ^ its (length vleafsl))
  in
    update_uset (selectn + 1) newpl (newuset,newresult)
  end

val test_flag = ref false
val scored_glob = ref (dempty IntInf.compare)

fun loop_scover_para ncore (bluen,redn) uset result = 
  if elength uset <= 0 then rev result else
  let
    val n = Int.min (!select_number1, elength uset)
    val ul = if !test_flag then 
      let 
        fun f x = dfind x (!scored_glob)
        val ulscore = dict_sort compare_rmax (map_assoc f (elist uset))  
      in
        map fst (first_n n ulscore)
      end
      else random_subset n (elist uset)
    val n' = Int.min (n,ncore)
    val param = ((bluen,redn),uset)
    val _ = clean_dir (selfdir ^ "/parallel_search")
    val pl = smlParallel.parmap_queue_extern n' genspec param ul
    val (newuset,newresult) = update_uset 0 pl (uset,result)
  in
    loop_scover_para ncore (bluen,redn) newuset newresult
  end


fun check_cover cover uset =
  let 
    val _ = print_endline "checking cover" 
    val instl = mk_fast_set IntInf.compare 
      (map fst (List.concat (map snd cover)))
  in
    if elist uset = instl 
    then ()
    else raise ERR "check_cover" ""
  end

fun compute_scover_para ncore size (bluen,redn) = 
  let
    val _ = if !test_flag 
            then scored_glob := init_scored size (bluen,redn)
            else ()
    val id = its bluen ^ its redn ^ its size
    val file = selfdir ^ "/enum/enum" ^ id
    val uset = enew IntInf.compare (map stinf (readl file));
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
    val cover = loop_scover_para ncore (bluen,redn) uset []
    val _ = check_cover cover uset
  in
    cover
  end

(* -------------------------------------------------------------------------
   Generalizations I/O
   ------------------------------------------------------------------------- *)

fun read_cover size (bluen,redn) =
  let 
    val file = selfdir ^ "/gen/gen" ^ 
      its bluen ^ its redn ^ its size
    val sl = readl file
    fun f s = 
      let 
        val sl1 = String.tokens Char.isSpace s
        val sll2 = map (String.tokens (fn x => x = #"_")) (tl sl1)
        fun g sl2 = (stinf (hd sl2), map string_to_int (tl sl2))
      in
        (stinf (hd sl1), map g sll2)
      end
  in
    map f sl
  end
  
fun read_par size (bluen,redn) =
  let 
    val file = selfdir ^ "/gen/gen" ^ 
      its bluen ^ its redn ^ its size
    val sl = readl file
    fun f s = 
      let val sl1 = String.tokens Char.isSpace s in
        stinf (hd sl1)
      end
  in
    map f sl
  end  

fun write_cover size (bluen,redn) cover = 
  let 
    val dir = selfdir ^ "/gen"
    val _ = mkDir_err dir
    val file = dir ^ "/gen" ^ its bluen ^ its redn ^ its size
    fun f (p,cperml) = 
      let fun g (c,perm) = infts c ^ "_" ^ 
        String.concatWith "_" (map its perm) 
      in
        String.concatWith " " (infts p :: map g cperml)
      end
  in
    mkDir_err dir;
    writel file (map f cover)
  end  

(* -------------------------------------------------------------------------
   Generalization main function
   ------------------------------------------------------------------------- *)

fun gen (bluen,redn) (minsize,maxsize) =  
  let
    fun f size =
      let
        val _ = print_endline ("size " ^ its size)
        val cover = compute_scover_para ncore size (bluen,redn)
      in
        write_cover size (bluen,redn) cover
      end  
  in
    ignore (range (minsize,maxsize,f))
  end
  

(*
load "gen"; open sat aiLib kernel graph gen;

test_flag := true;
select_number1 := 313;
select_number2 := 1;
val (_,t35) = add_time (gen (3,5)) (10,10);

select_number1 := 1000;
select_number2 := 100;
val (_,t44) = add_time (gen (4,4)) (14,14);

(* experiment e4e4test *)
*)


end (* struct *)






