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

(* global parameters *)
val memory = iflag "memory" 5000
val ncore = (string_to_int (dfind "ncore" configd) handle NotFound => 32)
val _ = smlExecScripts.buildheap_options :=  "--maxheap " ^ its memory

(* used in sat.sml (default is unlimited) *)
val real_time = rflag "real_time" 0.0
val abstract_time = iflag "abstract_time" 0

(* -------------------------------------------------------------------------
   Logging
   ------------------------------------------------------------------------- *)

val disable_log = ref false

val logfile = ref (selfdir ^ "/aaa_log")
val store_log = ref true

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
   Efficient subsets computation
   ------------------------------------------------------------------------- *)

fun subsets_of_size_large_aux n (l,ln) = 
  if n > ln then [] else if n = ln then [l] else
  (
  case l of
    [] => if n = 0 then [[]] else []
  | a :: m => 
    let
      val l1 = map (fn subset => a::subset) 
        (subsets_of_size_large_aux (n - 1) (m,ln-1))
      val l2 = subsets_of_size_large_aux n (m,ln-1)
    in
      l1 @ l2
    end  
  )

fun subsets_of_size_large n l =  subsets_of_size_large_aux n (l, length l)

fun extend_subset_aux ntop lref subset extl len = 
  if len < ntop then () else
  case extl of
    [] => ()
  | a :: m => (lref := (a :: subset,m,len) :: !lref; 
               extend_subset_aux ntop lref subset m (len-1));

fun extend_subset ntop lref (subset,extl,len) = 
  extend_subset_aux ntop lref subset extl len;

fun extend_subsetl ntop subsetl = 
  let val lref = ref [] in
    app (extend_subset ntop lref) subsetl;
    rev (!lref)
  end;

fun subsets_of_size_small ntop l = 
  let 
    val len = length l
    fun loop n subsetl =
      if n <= 0 then subsetl else loop (n-1) (extend_subsetl ntop subsetl)
  in
    if ntop < 0 orelse len < ntop then [] 
    else map (rev o #1) (loop ntop [([],l,len)])
  end
  
fun subsets_of_size n l =
  if n <= length l div 2 
  then subsets_of_size_small n l 
  else subsets_of_size_large n l

(*
load "kernel"; open aiLib kernel; 
val (l,t) = add_time (subsets_of_size 3) (List.tabulate (7,I));
*)


(* -------------------------------------------------------------------------
   Other tools
   ------------------------------------------------------------------------- *)

fun range (a,b,f) = List.tabulate (b-a+1,fn i => f (i+a));

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

val arb0 = IntInf.fromInt 0;
val arb1 = IntInf.fromInt 1;

fun split_pair c s = pair_of_list (String.tokens (fn x => x = c) s)
fun split_triple c s = triple_of_list (String.tokens (fn x => x = c) s)

(* -------------------------------------------------------------------------
   General parallelizer for function : unit -> string -> string
   as long as the function can be named
   ------------------------------------------------------------------------- *)

fun write_string file s = writel file [s]
fun read_string file = singleton_of_list (readl file)
fun write_unit file () = ()
fun read_unit file = ()

fun stringspec_fun_default (s:string) = "default"
val stringspec_fun_glob = ref stringspec_fun_default
val stringspec_funname_glob = ref "kernel.stringspec_fun_default"

val stringspec : (unit, string, string) smlParallel.extspec =
  {
  self_dir = selfdir,
  self = "kernel.stringspec",
  parallel_dir = selfdir ^ "/parallel_search",
  reflect_globals = (fn () => "(" ^
    String.concatWith "; "
    [
    "smlExecScripts.buildheap_dir := " ^ 
       mlquote (!smlExecScripts.buildheap_dir),
    "kernel.stringspec_fun_glob := " ^ (!stringspec_funname_glob)
    ]
    ^ ")"),
  function = let fun f () s = (!stringspec_fun_glob) s in f end,
  write_param = write_unit,
  read_param = read_unit,
  write_arg = write_string,
  read_arg = read_string,
  write_result = write_string,
  read_result = read_string
  }

fun parmap_sl ncore funname sl =
  let
    val dir = selfdir ^ "/exp/reserved_stringspec"
    val _ = app mkDir_err [(selfdir ^ "/exp"), dir] 
    val _ = stringspec_funname_glob := funname
    val _ = smlExecScripts.buildheap_dir := dir
    val slo = smlParallel.parmap_queue_extern ncore stringspec () sl
  in
    slo
  end

fun test_fun s = (implode o rev o explode) s




end (* struct *)
