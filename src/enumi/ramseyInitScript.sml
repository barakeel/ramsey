(* ========================================================================= *)
(* Enumeration of ramsey graphs: initialization                              *)
(* ========================================================================= *)

open HolKernel boolLib kernel enump ramseyDefTheory

val _ = new_theory "ramseyEnumInit"

val R355 = save_thm ("R355", R_THM 5 (3,5))
val R356 = save_thm ("R356", NEXT_R_THM 6 (3,5) R355)
val R357 = save_thm ("R357", NEXT_R_THM 7 (3,5) R356)
val R358 = save_thm ("R358", NEXT_R_THM 8 (3,5) R357)
val R359 = save_thm ("R359", NEXT_R_THM 9 (3,5) R358)
val R3510 = save_thm ("R3510", NEXT_R_THM 10 (3,5) R359)
val R3511 = save_thm ("R3511", NEXT_R_THM 11 (3,5) R3510)
val R3512 = save_thm ("R3512", NEXT_R_THM 12 (3,5) R3511)
val R3513 = save_thm ("R3513", NEXT_R_THM 13 (3,5) R3512)
val R3514 = save_thm ("R3514", NEXT_R_THM 14 (3,5) R3513)

val R444 = save_thm ("R444", R_THM 4 (4,4))
val R445 = save_thm ("R445", NEXT_R_THM 5 (4,4) R444)
val R446 = save_thm ("R446", NEXT_R_THM 6 (4,4) R445)
val R447 = save_thm ("R447", NEXT_R_THM 7 (4,4) R446)

val _ = export_theory ()
