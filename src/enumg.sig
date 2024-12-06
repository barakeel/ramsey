signature enumg =
sig
  
  (*  
  val enumgspec : (int * int, int * IntInf.int list, unit) smlParallel.extspec
  val enum : (int * int) -> unit
  
  val write_enumg : int -> int * int -> IntInf.int list -> unit
  val read_enumg : int -> int * int -> IntInf.int list
  *)
  val write_infl : string -> IntInf.int list -> unit
  val read_infl : string -> IntInf.int list
  
  val iter_cover : IntInf.int list -> IntInf.int list
  val extend : IntInf.int list -> IntInf.int list
  
  (* parallelization *)
  val enumgspec : (IntInf.int Redblackset.set, IntInf.int, IntInf.int list)      
    smlParallel.extspec
  val cover_para: int -> IntInf.int Redblackset.set -> IntInf.int list
  
  val enumg : string -> int * int -> int -> int -> unit
  
end
