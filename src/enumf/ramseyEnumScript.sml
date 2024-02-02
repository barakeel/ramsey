(* ========================================================================= *)
(* Enumeration of ramsey graphs: (after running parallel lemmas *)
(* ========================================================================= *)

open HolKernel boolLib kernel enump ramseyDefTheory

val _ = new_theory "ramseyEnum"

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

fun collect_44k k = 
  let
    val filel = filter (String.isSuffix "Theory.sml") 
      (listDir (selfdir ^ "/enump"))
    val thyl = map (fn s => fst (split_string "Theory" s)) filel
    val prefix = "ramseyEnum44" ^ its k
    val thyl8 = filter (String.isPrefix prefix) thyl
    val _ = app load (map (fn x => selfdir ^ "/enump/" ^ x ^ "Theory") thyl8)
    val sthml = List.concat (map DB.thms thyl8)
    fun f s = string_to_int (snd (split_string "_" s))
    val ithml = map_fst f sthml
  in
     map snd (dict_sort (fst_compare Int.compare) ithml)
  end
 
val R448 = save_thm ("R448", NEXT_R_THM_PAR 8 (4,4) R447 (collect_44k 8))
val R449 = save_thm ("R449", NEXT_R_THM_PAR 9 (4,4) R448 (collect_44k 9))
val R4410 = save_thm ("R4410", NEXT_R_THM_PAR 10 (4,4) R449 (collect_44k 10))
val R4411 = save_thm ("R4411", NEXT_R_THM_PAR 11 (4,4) R4410 (collect_44k 11))
val R4412 = save_thm ("R4412", NEXT_R_THM_PAR 12 (4,4) R4411 (collect_44k 12))
val R4413 = save_thm ("R4413", NEXT_R_THM_PAR 13 (4,4) R4412 (collect_44k 13))
val R4414 = save_thm ("R4414", NEXT_R_THM_PAR 14 (4,4) R4413 (collect_44k 14))
val R4415 = save_thm ("R4415", NEXT_R_THM_PAR 15 (4,4) R4414 (collect_44k 15))
val R4416 = save_thm ("R4416", NEXT_R_THM_PAR 16 (4,4) R4415 (collect_44k 16))
val R4417 = save_thm ("R4417", NEXT_R_THM_PAR 17 (4,4) R4416 (collect_44k 17))
val R4418 = save_thm ("R4418", NEXT_R_THM_PAR 18 (4,4) R4417 (collect_44k 18))


val _ = export_theory ()
