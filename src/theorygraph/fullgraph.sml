load "theorygraphIO"; load "kernel"; 
open aiLib kernel theorygraphIO;
val ERR = mk_HOL_ERR "fullgraph";

(* -------------------------------------------------------------------------
   Export the theory dependencies of the final theory (without missing
   parents)
   ------------------------------------------------------------------------- *)

(* restart hol *)
(*
load "theorygraphIO";
load "../mergef/r45_equals_25Theory";
theorygraphIO.write_theorygraph "r45_equals_25";
*)
(* restart hol *)

(* -------------------------------------------------------------------------
   Export the theorygraph of the missing parents
   ------------------------------------------------------------------------- *)

fun write_script3510 i = 
  let 
    val thyname = "r45_degree10_" ^ its i
    val thyfile = "../merge3510/" ^ thyname
  in
    writel (selfdir ^ "/theorygraph/script3510_" ^ its i)
      ["load \"theorygraphIO\" ;", 
       "load " ^ mlquote thyfile ^ ";",
       "theorygraphIO.write_theorygraph " ^ mlquote thyname ^ ";"]
  end
  
fun run_script3510 i =
  let 
    val thyname = "r45_degree10_" ^ its i
    val thyfile = "../merge3510/" ^ thyname
  in
    write_script3510 i;
    smlExecScripts.exec_script thyfile
  end  


(* -------------------------------------------------------------------------
   Reading back all theory graphs
   ------------------------------------------------------------------------- *)

fun find_thyid thy thygraph =
  valOf (List.find (fn ((a,_,_),_) => a = thy) thygraph)

fun read_extra thy = 
  let 
    val thygraph = read_theorygraph thy
    val node = find_thyid thy thygraph
  in  
    (node,thygraph)
  end
  
val (r45node,r45graph) = read_extra "r45_equals_25"

val degree10l = List.tabulate (43, fn i => 
  read_extra ("r45_degree10_" ^ its i))
val degree10nodel = map (fst o fst) degree10l;

val degree12l = List.tabulate (12, fn i => 
  read_extra ("r45_degree12_" ^ its i))
val degree12nodel = map (fst o fst) degree12l;

(* -------------------------------------------------------------------------
   Add missing parents of the r45_equals_25 theory and its theory graph.
   ------------------------------------------------------------------------- *)

fun add_parent (newp,(n,pl)) = 
  if not (mem (#1 newp) (map #1 pl)) 
  then (n, newp :: pl)
  else raise ERR "add_parent" ""

fun r45node' = fold add_parent r45node (degree10nodel @ degree12nodel);
fun r45graph' = map (fn x => if x = r45node then r45node' else x) r45graph;

(* -------------------------------------------------------------------------
   Checks that all the theory graphs can be combined without any cycles
   ------------------------------------------------------------------------- *)

val degree10thygraphl = map snd degree10l;
val degree12thygraphl = map snd degree12l;
val r45thygraph = r45graph';

fun thyid_compare (thyid1,thyid2) = 
  triple_compare String.compare Arbnum.compare Arbnum.compare

fun combine_theorygraph thygraphl =
  let 
    val dtop = dempty thyid_compare
    val prevntop = dlength d
    val ltop = List.concat thygraphl
  in
    fun loop l' l prevn d =
      if null l andalso null l' then dlist d
      else if null l then 
        if prevn = dlength d 
        then raise ERR "combine_theorygraph" "cycle"
        else loop [] (rev l') (dlength d) d
      else
        let val (node,parentl) = hd l in
          case dfindo node d of
            NONE => if all (fn x => dmem x (!d)) parentl
                    then loop l' (tl l) (dadd node parentl d)
                    else loop (hd l :: l') (tl l) d
          | SOME (_,parl) => 
            if elist (enew thyid_compare parl) = 
               elist (enew thyid_compare parentl)
            then loop l' (tl l) d
            else raise ERR "combine_theorygraph" "different sets of parents"   
        end
   in
     loop [] ltop prevntop dtop
   end
   
val finaltheorygraph = combine_theorygraph 
  [degree10thygraphl,degree12thygraphl,r45thygraph];
    
length finaltheorygraph;





