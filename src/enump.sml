structure enump :> enump =
struct   

open HolKernel Abbrev boolLib aiLib kernel graph nauty syntax sat enum gen
val ERR = mk_HOL_ERR "enump"

fun create_pard size (bluen,redn) = 
  let val parl = read_par size (bluen,redn) in
    if null parl then dempty IntInf.compare else
    let
      val id = its bluen ^ its redn ^ its size
      val conjdef = DB.fetch "ramseyDef"  ("G" ^ id ^ "_DEF")
      val f = UNDISCH o fst o EQ_IMP_RULE o SPEC_ALL
      val thml = map (UNDISCH_ALL o SPEC_ALL) (CONJUNCTS (f conjdef))
      val gthml = combine (parl,thml)
    in
      dnew IntInf.compare gthml
    end
  end

(* -------------------------------------------------------------------------
   Proves that ramsey clauses on bigger graphs imply ramsey clauses
   on smaller graphs
   ------------------------------------------------------------------------- *)

fun Cid size (bluen,redn) b = 
  "C" ^ its bluen ^ its redn ^ its size ^ (if b then "b" else "r")
  
fun C_SMALLER size (bluen,redn) b = 
  let
    val colorn = if b then bluen else redn
    val sbig = Cid (size+1) (bluen,redn) b
    val ssmall = Cid size (bluen,redn) b
    val defbig = DB.fetch "ramseyDef" (sbig ^ "_DEF")
    val defsmall = DB.fetch "ramseyDef" (ssmall ^ "_DEF")
    val f = rhs o snd o strip_forall o concl
    val thm1 = UNDISCH_ALL (SPEC_ALL (ASSUME (f defbig)))
    val lemma = LESS_THAN_NEXT size
    val vl = List.tabulate (colorn,X)
    val lemmal = map (fn x => UNDISCH (SPEC x lemma)) vl
    val thm2 = (foldl (uncurry PROVE_HYP) thm1) lemmal
    val terml = (fst o strip_imp) ((snd o strip_forall) (f defsmall))
    val thm3 = foldl (uncurry DISCH) thm2 (rev terml)
    val thm4 = EQ_MP (SYM (SPEC_ALL defsmall)) (GENL vl thm3)
    val thm5 = PROVE_HYP_EQ (SPEC_ALL defbig) thm4
  in
    thm5
  end

(* -------------------------------------------------------------------------
   Construct Ramsey theorems from Ramsey theorems at smaller sizes.
   ------------------------------------------------------------------------- *)

(* serial version *)
fun R_THM size (bluen,redn) =
  let
    val cover = read_cover size (bluen,redn)
    val pard = create_pard size (bluen,redn)
    val _ = init_gthmd pard cover
    val _ = (iso_flag := false; debug_flag := false; proof_flag := true)
    val _ = sat_solver size (bluen,redn)
  in
    ELIM_COND size (!final_thm)
  end

fun NEXT_R_THM size (bluen,redn) prevthm = 
  let
    val gs = "G" ^ its bluen ^ its redn ^ its (size - 1)
    val prevparl = read_par (size - 1) (bluen,redn)
    val cover = read_cover size (bluen,redn)
    val (pard,t) = add_time (create_pard size) (bluen,redn)
    val _ = init_gthmd pard cover
    fun f1 mi = 
      let 
        val m = unzip_mat mi
        val _ = (iso_flag := false; debug_flag := false; proof_flag := true)
        val _ = sat_solver_edgecl (mat_to_edgecl m) size (bluen,redn) 
      in
        ELIM_COND_GRAPH m (!final_thm)
      end
    val thml0 = map f1 prevparl
    val thm2 = LIST_CONJ thml0;
    val prevgdef = DB.fetch "ramseyDef" (gs ^ "_DEF")
    val prevgthm = (snd o EQ_IMP_RULE o SPEC_ALL) prevgdef
    val thm3 = MP prevgthm thm2
    val thm4 = PROVE_HYP thm3 prevthm
    val (thmb,thmr) = (C_SMALLER (size - 1) (bluen,redn) true, 
                       C_SMALLER (size - 1) (bluen,redn) false);
  in
    PROVE_HYPL [thmb,thmr] thm4
  end

(* parallel version *)
fun INIT_NEXT_R_THM_ONE size (bluen,redn) =
  let
    val gs = "G" ^ its bluen ^ its redn ^ its (size - 1)
    val (cover,t) = add_time (read_cover size) (bluen,redn)
    val _ = print_endline ("read_cover: " ^ rts_round 4 t)
    val (pard,t) = add_time (create_pard size) (bluen,redn)
    val _ = print_endline ("create_pard: " ^ rts_round 4 t)
    val (_,t) = add_time (init_gthmd pard) cover
    val _ = print_endline ("init_gthm: " ^ rts_round 4 t)
  in
    ()
  end
  
fun NEXT_R_THM_ONE size (bluen,redn) prevpar = 
  let
    val graph = unzip_mat prevpar
    val edgecl = mat_to_edgecl graph
    val _ = (iso_flag := false; debug_flag := false; proof_flag := true)
    val (_,t) = add_time (sat_solver_edgecl edgecl size) (bluen,redn)
    val _ = print_endline ("sat_solver_edgecl: " ^ rts_round 4 t)
    val (thm,t) = add_time (ELIM_COND_GRAPH graph) (!sat.final_thm) 
    val _ = print_endline ("ELIM_COND_GRAPH: " ^ rts_round 4 t)
  in
    thm
  end
  
fun NEXT_R_THM_PAR size (bluen,redn) prevthm thml = 
  let
    val gs = "G" ^ its bluen ^ its redn ^ its (size - 1)
    val thm2 = LIST_CONJ thml;
    val prevgdef = DB.fetch "ramseyDef" (gs ^ "_DEF")
    val prevgthm = (snd o EQ_IMP_RULE o SPEC_ALL) prevgdef
    val thm3 = MP prevgthm thm2
    val thm4 = PROVE_HYP thm3 prevthm
    val (thmb,thmr) = (C_SMALLER (size - 1) (bluen,redn) true, 
                       C_SMALLER (size - 1) (bluen,redn) false);
  in
    PROVE_HYPL [thmb,thmr] thm4
  end 

fun write_enumscript size (bluen,redn) (batchi,igraphl) = 
  let 
    val id = its bluen ^ its redn ^ its size
    val batchs = id ^ "_" ^ its batchi
    val thyname = "ramseyEnum" ^ batchs
    val filename = selfdir ^ "/enump/" ^ thyname ^ "Script.sml"
    val args = its size ^ " (" ^ its bluen ^ "," ^ its redn ^ ")"
    val open_cmd = ["open HolKernel boolLib kernel enump ramseyDefTheory"]
    val newtheory_cmd = ["val _ = new_theory " ^ mlquote thyname]
    val init_cmd =  ["val _ = INIT_NEXT_R_THM_ONE " ^ args]
    fun save_cmd (i,graph) = 
      let 
        val thmname = "R" ^ id ^ "_" ^ its i 
        val graphs =  "(stinf " ^ mlquote (infts graph) ^ ")"
      in
        "val _ = save_thm (" ^  mlquote thmname ^ 
        ", NEXT_R_THM_ONE " ^ args ^ " " ^ graphs ^ ")"
      end
    val export_cmd = ["val _ = export_theory ()"]
  in
    writel filename (open_cmd @ newtheory_cmd @ init_cmd @
                     map save_cmd igraphl @ export_cmd)
  end

fun write_enumscripts batchsize size (bluen,redn) = 
  let
    val _ = mkDir_err (selfdir ^ "/enump")
    val parl = read_par (size-1) (bluen,redn)
    val ncut = (length parl div batchsize) + 1
    val _ = print_endline ("par: " ^ its (length parl))
    val l = number_fst 0 (cut_modulo ncut (number_fst 0 parl))
  in
    app (write_enumscript size (bluen,redn)) l
  end

fun collect_44k k = 
  let
    val enumpdir = selfdir ^ "/enump"
    val filel1 = listDir (selfdir ^ "/enump")
    val filel2 = filter (String.isSuffix "Theory.sml") filel1
    val thyl = map (fn s => fst (split_string "Theory" s)) filel2
    val prefix = "ramseyEnum44" ^ its k
    val thyl8 = filter (String.isPrefix prefix) thyl
    val sthml = List.concat (map DB.thms thyl8)
    fun f s = string_to_int (snd (split_string "_" s))
    val ithml = map_fst f sthml
  in
    map snd (dict_sort (fst_compare Int.compare) ithml)
  end

fun write_enumfinalscript () =
  let
    val enumpdir = selfdir ^ "/enump"
    val enumfdir = selfdir ^ "/enumf"
    val filel1 = listDir enumpdir
    val filel2 = filter (String.isSuffix "Theory.sml") filel1 
    val thyl = map (fn s => fst (split_string ".sml" s)) filel2 
    val s = String.concatWith " " ("open" :: thyl)
    val cmd = 
      "cat open_template ramseyEnumScript_template > ramseyEnumScript.sml"
  in
    writel (enumfdir ^ "/open_template") [s];
    cmd_in_dir enumfdir cmd
  end

(* -------------------------------------------------------------------------
   Generating scripts
   ------------------------------------------------------------------------- *)

(*
load "enump"; open kernel enump;
val _ = range (8, 18, fn size => write_enumscripts 50 size (4,4));
*)

(* -------------------------------------------------------------------------
   Run scripts
   ------------------------------------------------------------------------- *)

(*
cd enump
echo "INCLUDES = .. ../def" > Holmakefile
../../HOL/bin/Holmake --no_prereqs -j 40 | tee ../aaa_log_enump
cd ..
*)

(* -------------------------------------------------------------------------
   Look at a theorem
   ------------------------------------------------------------------------- *)

(*
load "enump/ramseyEnum4413_0Theory";
val sl = map fst (DB.thms "ramseyEnum4413_0");
show_assums := true;
val thm = DB.fetch "ramseyEnum4413_0" "R4413_0";
*)
  
end (* struct *)
