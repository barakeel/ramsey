(* ===================================================================== *)
(* Merging lemmas to prove that degree 10 is impossible.                  *)
(* ===================================================================== *)

open HolKernel Abbrev boolLib merge

val _ = new_theory "r45_degree10"
val _ = save_thm ("r45_degree10", IMPOSSIBLE_REG_35 10)
val _ = export_theory ()
