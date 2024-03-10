(* ===================================================================== *)
(* Merging lemmas to prove that degree 12 is impossible.                 *)
(* ===================================================================== *)

open HolKernel Abbrev boolLib merge

val _ = new_theory "r45_degree12"
val _ = save_thm ("r45_degree12", IMPOSSIBLE_REG_35 12)
val _ = export_theory ()
