(* =========================================================================
   Post-process the result each glueing theorem before saving them to disk
   ========================================================================= *)
   
structure gluepost :> gluepost =
struct   

open HolKernel Abbrev boolLib bossLib aiLib kernel syntax graph sat gen 
val ERR = mk_HOL_ERR "gluepost"

fun get_ij atom = 
  let val (x1,x2) = pair_of_list (snd (strip_comb atom)) in
    (Xnum x1, Xnum x2)
  end

fun dest_lit lit = 
  let 
    val b = is_neg lit 
    val atom = if b then dest_neg lit else lit
    val (i1,i2) = get_ij atom
  in
    ((i1,i2), if (not b) then 1 else 2)
  end

val NOT_NOT_THM = DECIDE ``!x. ~(~x) <=> x``
val OR_FALSE_THM = DECIDE ``!x. x \/ F <=> x``
val C4524b_ASM = ASSUME (syntax.noclique 24 (4,true)) 
val C4524r_ASM = ASSUME (syntax.noclique 24 (5,false))

fun OR_IMP_CONV tm = 
  let
    val alttm = list_mk_disj (strip_disj tm @ [F]) 
    val thm = PURE_REWRITE_CONV [DISJ_EQ_IMP] alttm
  in
    PURE_REWRITE_RULE [OR_FALSE_THM,NOT_NOT_THM] thm
  end;

fun get_cassume tm =
  let 
    val litl = fst (strip_imp tm) 
    val edgecl = map dest_lit litl 
    val nl = List.concat (map (fn ((a,b),_) => [a,b]) edgecl)
    val (il,b) = (mk_fast_set Int.compare nl, snd (hd edgecl) = 1)
    val cthm0 = if b then C4524b_ASM else C4524r_ASM
    val xl = map X il
  in
    DISCHL litl (UNDISCH_ALL (SPECL xl cthm0))
  end

fun to_first_order thm = 
  let
    fun get_atom x = if is_neg x then dest_neg x else x
    val litl = mk_fast_set Term.compare 
      (List.concat (map (fst o strip_imp) (hyp thm)))
    val atoml = mk_fast_set Term.compare (map get_atom litl)
    fun sate_to_foe v = 
      let val (a,b,c) = (triple_of_list o String.tokens (fn x => x = #"_") 
        o fst o dest_var) v
      in
        hvarij (string_to_int b, string_to_int c)
      end
    fun f x = {redex = x, residue = sate_to_foe x}
    val sub = map f atoml
  in
    INST sub thm
  end

fun post gluethm0 = 
  let
    val gluethm1 = UNDISCH_SPLIT gluethm0
    val lemmal = map (UNDISCH o snd o EQ_IMP_RULE o OR_IMP_CONV) (hyp gluethm1)
    val gluethm1' = PROVE_HYPL lemmal gluethm1
    val gluethm2 = to_first_order gluethm1'
    val lemmal = map get_cassume (hyp gluethm2)
    val gluethm3 = PROVE_HYPL lemmal gluethm2
  in
    gluethm3
  end
  

end (* struct *)




