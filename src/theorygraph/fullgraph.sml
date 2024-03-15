load "theorygraphIO"; load "kernel"; 
open aiLib kernel theorygraphIO;

fun add_parent (newp,(n,pl)) = 
  if not (mem (#1 newp) (map #1 pl)) 
  then (n, newp :: pl)
  else raise ERR "add_parent" ""
  
fun add_parentl (n,pl) parentl = fold add_parent (n,pl) parentl 


(* *) 
load "../mergef/r45_equals_25Theory";


write_script 

