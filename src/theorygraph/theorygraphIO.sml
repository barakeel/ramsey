structure theorygraphIO :> theorygraphIO = struct

open HolKernel boolLib kernel aiLib
val ERR = mk_HOL_ERR "theorygraphIO"

type thyid = string * Arbnum.num * Arbnum.num

fun thyid_of_thy thy = 
  let val {sec,usec} = Portable.dest_time (stamp thy) in (thy,sec,usec) end

fun thyid_to_string (name,t1,t2) = 
  String.concatWith " " [name,Arbnum.toString t1,Arbnum.toString t2]

fun thyid_from_string s = 
  let val (name,t1s,t2s) = triple_of_list (String.tokens Char.isSpace s) in
    (name, Arbnum.fromString t1s, Arbnum.fromString t2s)
  end

fun node_to_string (thyid,thyidl) =
  String.concatWith "," (map thyid_to_string (thyid :: thyidl))
  
fun node_from_string s = 
  let val sl = String.tokens (fn x => x = #",") s in
    (thyid_from_string (hd sl), map thyid_from_string (tl sl))
  end

fun theorygraph_of_thy thy = 
  let 
    val thyl = ancestry thy 
    fun f x = (thyid_of_thy x, map thyid_of_thy (parents x))
  in 
    map f (thy :: thyl)
  end
  
fun file_of_thy thy = selfdir ^ "/theorygraph/" ^ thy ^ ".graph"  
  
fun write_theorygraph filename thygraph =
  writel filename (map node_to_string thygraph)  
  
fun read_theorygraph filename =
  map node_from_string (readl filename)  
  
fun write_theorygraph_nocheck thy thygraph =
  writel (file_of_thy thy) (map node_to_string thygraph)
  
fun read_theorygraph_of_thy thy =
  map node_from_string (readl (file_of_thy thy))

fun write_theorygraph_of_thy thy = 
  let
    val thygraph = theorygraph_of_thy thy
    val _ = write_theorygraph_nocheck thy thygraph
    val newthygraph = read_theorygraph thy
  in
    if thygraph <> newthygraph then raise ERR "export_theorygraph" "" else ()
  end  
  
  
end
