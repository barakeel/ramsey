structure kernel :> kernel =
struct

open HolKernel Abbrev boolLib aiLib dir;
val ERR = mk_HOL_ERR "kernel";
               
val selfdir = dir.selfdir 

(* -------------------------------------------------------------------------
   Config file
   ------------------------------------------------------------------------- *)

val configd = 
  if exists_file (selfdir ^ "/config") then 
    let 
      val sl = readl (selfdir ^ "/config")
      fun f s = SOME (pair_of_list (String.tokens Char.isSpace s)) 
        handle HOL_ERR _ => NONE
    in
      dnew String.compare (List.mapPartial f sl)
    end
  else dempty String.compare

fun bflag s b = 
  string_to_bool (dfind s configd) handle NotFound => b
fun iflag s i = 
  string_to_int (dfind s configd) handle NotFound => i
fun rflag s r = 
  valOf (Real.fromString (dfind s configd)) handle NotFound => r

val real_time = rflag "real_time" 0.0
val abstract_time = iflag "abstract_time" 0
val memory = iflag "memory" 10000
val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)

(* -------------------------------------------------------------------------
   Logging
   ------------------------------------------------------------------------- *)

val disable_log = ref false

val logfile = ref (selfdir ^ "/aaa_log")
val store_log = ref false

fun log s = 
  if !disable_log then () 
  else if !store_log then (print_endline s; append_endline (!logfile) s)
  else print_endline s


(* -------------------------------------------------------------------------
   Dictionaries shortcuts
   ------------------------------------------------------------------------- *)

type ('a,'b) dict = ('a, 'b) Redblackmap.dict
fun eaddi x d = d := eadd x (!d)
fun ememi x d = emem x (!d)
fun daddi k v d = d := dadd k v (!d) 
fun dmemi x d = dmem x (!d)
fun dfindo k d = Redblackmap.peek (d,k)
fun ereml kl d = foldl (uncurry erem) d kl;
fun dreml kl d = foldl (uncurry drem) d kl;

(* -------------------------------------------------------------------------
   Other tools
   ------------------------------------------------------------------------- *)

fun range (a,b,f) = List.tabulate (b-a+1,fn i => f (i+a));

fun subsets_of_size_aux n (l,ln) = 
  if n > ln then [] else if n = ln then [l] else
  (
  case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) 
        (subsets_of_size_aux (n - 1) (m,ln-1))
      val l2 = subsets_of_size_aux n (m,ln-1)
    in
      l1 @ l2
    end  
  )

fun subsets_of_size n l =  subsets_of_size_aux n (l, length l)

val infts = IntInf.toString
val stinf = valOf o IntInf.fromString
val streal = valOf o Real.fromString 

fun ilts il = String.concatWith " " (map its il)
fun stil s = map string_to_int (String.tokens Char.isSpace s)

val timer_glob1 = ref 0.0
val timer_glob2 = ref 0.0
val timer_glob3 = ref 0.0
val timer_glob4 = ref 0.0
val timer_glob5 = ref 0.0



  
end (* struct *)
