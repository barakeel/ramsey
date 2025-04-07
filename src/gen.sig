signature gen =
sig

  type mat = int Array2.array
  type vleafs = int * int * (IntInf.int * int list) list  
  
  (* parameters *)
  val maxhole : int ref
  val exponent : real ref
  val select_number1 : int ref
  val select_number2 : int ref
  val mincover : real ref
  val select_basic : bool ref
  
  
  (* scoring number of shapes *)
  val get_average35 : IntInf.int list -> ((int * int) * real) list
  val get_average44 : IntInf.int list -> ((int * int) * real) list
  val difficulty_pair : IntInf.int * IntInf.int -> real
  
  (* simple generalization *)
  val extra_clausel : ((int * int) * int) list list ref
   
  val gen_simple : int * int ->
    ((int * int) * int) list -> int -> IntInf.int -> IntInf.int -> 
    int -> (int * int) list
  
  (* parallelization *)
  val genspec : ((int * int) * IntInf.int Redblackset.set, IntInf.int, 
    IntInf.int * vleafs list) smlParallel.extspec
  val compute_scover_para : int -> int -> int * int -> 
    (IntInf.int * (IntInf.int * int list) list) list
  
  (* I/O *)
  val write_cover :  int -> int * int ->
    (IntInf.int * (IntInf.int * int list) list) list -> unit
  val read_cover : int -> int * int -> 
    (IntInf.int * (IntInf.int * int list) list) list
  val read_par : int -> int * int -> IntInf.int list
  
  (* main *)
  val gen : int * int -> int * int -> unit
  
end
