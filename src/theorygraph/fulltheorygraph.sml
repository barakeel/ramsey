(* -------------------------------------------------------------------------
   Export the theory dependencies of the final theory (without missing
   parents)
   ------------------------------------------------------------------------- *)

(* restart hol *)
load "theorygraphIO";
load "../mergef/r45_equals_25Theory";
theorygraphIO.write_theorygraph_of_thy "r45_equals_25";

(* -------------------------------------------------------------------------
   Export the theorygraph of the missing parents.
   ------------------------------------------------------------------------- *)

(* restart hol *)
load "theorygraphIO"; load "kernel"; load "smlExecScripts"; load "smlParallel";
open aiLib kernel theorygraphIO;
  
fun run_script3510 i =
  let 
    val dir = selfdir ^ "/theorygraph"
    val script = dir ^ "/script3510_" ^ its i ^ ".sml"
    val thyname = "r45_degree10_" ^ its i
    val thyfile = "../merge3510/" ^ thyname ^ "Theory"
    val _ = smlExecScripts.buildheap_dir := dir ^ "/buildheap"
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
  in
    writel script
      ["load \"theorygraphIO\" ;", 
       "load " ^ mlquote thyfile ^ ";",
       "theorygraphIO.write_theorygraph_of_thy " ^ mlquote thyname ^ ";"];
    smlExecScripts.exec_script script
  end; 
  
val _ = smlParallel.parapp_queue 43 run_script3510 (List.tabulate (43,I));

fun run_script3512 i =
  let 
    val dir = selfdir ^ "/theorygraph"
    val script = dir ^ "/script3512_" ^ its i ^ ".sml"
    val thyname = "r45_degree12_" ^ its i
    val thyfile = "../merge3512/" ^ thyname ^ "Theory"
    val _ = smlExecScripts.buildheap_dir := dir ^ "/buildheap"
    val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory
  in
    writel script
      ["load \"theorygraphIO\" ;", 
       "load " ^ mlquote thyfile ^ ";",
       "theorygraphIO.write_theorygraph_of_thy " ^ mlquote thyname ^ ";"];
    smlExecScripts.exec_script script
  end;

val _ = smlParallel.parapp_queue 12 run_script3512 (List.tabulate (12,I));


(* -------------------------------------------------------------------------
   Reading back all theory graphs
   ------------------------------------------------------------------------- *)

(* restart hol (not mandatory) *)
load "theorygraphIO"; load "kernel";
open aiLib kernel theorygraphIO;
val ERR = mk_HOL_ERR "fullgraph";

fun find_thyid thy thygraph =
  valOf (List.find (fn ((a,_,_),_) => a = thy) thygraph)

fun read_extra thy = 
  let 
    val thygraph = read_theorygraph_of_thy thy
    val node = find_thyid thy thygraph
  in  
    (node,thygraph)
  end;
  
val (r45node,r45graph) = read_extra "r45_equals_25";

val degree10l = List.tabulate (43, fn i => 
  read_extra ("r45_degree10_" ^ its i))
val degree10nodel = map (fst o fst) degree10l;

val degree12l = List.tabulate (12, fn i => 
  read_extra ("r45_degree12_" ^ its i))
val degree12nodel = map (fst o fst) degree12l;

(* -------------------------------------------------------------------------
   Add missing parents of the r45_equals_25 theory and its theory graph.
   ------------------------------------------------------------------------- *)

fun fst3 (a,b,c) = a;

fun add_parent (newp,(n,pl)) = 
  if not (mem (fst3 newp) (map fst3 pl)) 
  then (n, newp :: pl)
  else raise ERR "add_parent" "";

val r45node' = foldl add_parent r45node (degree10nodel @ degree12nodel);
val r45graph' = map (fn x => if x = r45node then r45node' else x) r45graph;

(* -------------------------------------------------------------------------
   Checks that all the theory graphs can be combined without any cycles
   ------------------------------------------------------------------------- *)

val degree10thygraphl = map snd degree10l;
val degree12thygraphl = map snd degree12l;
val r45thygraph = r45graph';

fun thyid_compare (thyid1,thyid2) = 
  triple_compare String.compare Arbnum.compare Arbnum.compare (thyid1,thyid2);

fun check_thyname node named = case dfindo (#1 node) named of 
    NONE => ()
  | SOME nodealt => 
    if node = nodealt then () 
    else raise ERR "check_thyname" ((#1 node) ^ 
      " theory exists in the graph with different time stamps")

fun combine_theorygraph thygraphl =
  let 
    val dtop = dempty thyid_compare
    val namedtop = dempty String.compare
    val ltop = List.concat thygraphl 
    val prevntop = length ltop 
    fun loop depth l' l prevn named d = case (l',l) of
        ([],[]) => dlist d
      | (_,[]) =>
        let val newprevn = length l' in
          if prevn = newprevn
          then raise ERR "combine_theorygraph" "cycle"
          else (
               print_endline (its (dlength d) ^ " theories at depth " ^ 
                              its depth); 
               loop (depth + 1) [] (rev l') newprevn named d)
               )
        end
      | (_, (node,parentl) :: m) => 
        let val _ = check_thyname node named in
          case dfindo node d of
            NONE => 
            if all (fn x => dmem x d) parentl
            then loop depth l' m prevn (dadd (#1 node) node named)
                   (dadd node parentl d)
            else loop depth ((node,parentl) :: l') m prevn named d
          | SOME parl => 
            if elist (enew thyid_compare parl) = 
               elist (enew thyid_compare parentl)
            then loop depth l' m prevn named d
            else raise ERR "combine_theorygraph" 
              ((#1 node) ^ " theory has different sets of parents") 
        end
   in
     loop 0 [] ltop prevntop namedtop dtop
   end;
   
val fulltheorygraph = combine_theorygraph 
  (List.concat [[r45thygraph], degree10thygraphl, degree12thygraphl]);

length fulltheorygraph;

write_theorygraph "fulltheorygraph.graph" fulltheorygraph;

