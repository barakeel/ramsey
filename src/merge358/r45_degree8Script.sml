(* ===================================================================== *)
(* Merging lemmas to prove that degree 8 is impossible.                  *)
(* ===================================================================== *)

open HolKernel Abbrev boolLib merge

val _ = new_theory "r45_degree8"
val _ = save_thm ("r45_degree8", IMPOSSIBLE 8)
val _ = export_theory ()
