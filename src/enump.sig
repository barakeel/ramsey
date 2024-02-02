signature enump =
sig
  
  include Abbrev
  type mat = int Array2.array
  
  val create_pard : int -> int * int -> (IntInf.int,thm) Redblackmap.dict
  
  (* creating R theorems (requires computed enum and cover) *)
  val C_SMALLER : int -> int * int -> bool -> thm
  (* serial version *)
  val R_THM : int -> int * int -> thm
  val NEXT_R_THM : int -> int * int -> thm -> thm 
  (* parallel version *)
  val INIT_NEXT_R_THM_ONE : int -> int * int -> unit
  val NEXT_R_THM_ONE : int -> int * int -> IntInf.int -> thm 
  val write_enumscript : int -> int * int -> 
    int * (int * IntInf.int) list -> unit
  val write_enumscripts : int -> int -> int * int -> unit
  val NEXT_R_THM_PAR : int -> int * int -> thm -> thm list -> thm
  val collect_44k : int -> thm list
  val write_enumfinalscript : unit -> unit
  
end
