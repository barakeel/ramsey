signature kernel =
sig

  include Abbrev
  (* directory *)
  val selfdir : string 
   
  (* global parameters *)
  val memory : int
  val ncore : int
  
  (* sat solving parameters *)
  val real_time : real
  val abstract_time : int
  
  (* logging *)
  val disable_log : bool ref
  val store_log : bool ref
  val logfile : string ref 
  val log : string -> unit 
  
  (* dictionaries shortcut*)
  type ('a,'b) dict = ('a, 'b) Redblackmap.dict
  val dfindo : 'a -> ('a, 'b) dict -> 'b option
  val eaddi : 'a -> 'a Redblackset.set ref -> unit
  val ememi : 'a -> 'a Redblackset.set ref -> bool
  val daddi : 'a -> 'b -> ('a, 'b) dict ref -> unit
  val dmemi : 'a -> ('a, 'b) dict ref -> bool
  val ereml : 'a list -> 'a Redblackset.set -> 'a Redblackset.set
  val dreml : 'a list -> ('a,'b) dict -> ('a,'b) dict
  
  (* other useful tools *)
  val range : int * int * (int -> 'a) -> 'a list
  val subsets_of_size : int -> 'a list -> 'a list list
  val infts : IntInf.int -> string
  val stinf : string -> IntInf.int
  val streal : string -> real
  val stil : string -> int list
  val ilts : int list -> string
  val arb0 : IntInf.int
  val arb1 : IntInf.int
  val split_pair : char -> string -> (string * string)
  val split_triple : char -> string -> (string * string * string)
  
  (* debugging timers *)
  val timer_glob1 : real ref
  val timer_glob2 : real ref
  val timer_glob3 : real ref
  val timer_glob4 : real ref
  val timer_glob5 : real ref
  
  (* parallelization of function of the type string to string *)
  val stringspec_fun_default : string -> string
  val stringspec_fun_glob : (string -> string) ref
  val stringspec_funname_glob : string ref
  val stringspec : (unit, string, string) smlParallel.extspec
  val parmap_sl : int -> string -> string list -> string list
  val test_fun : string -> string

  
end
