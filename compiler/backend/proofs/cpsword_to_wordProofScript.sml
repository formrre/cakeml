(*
  Correctness proof for cpsword_to_word
*)

open preamble cpswordSemTheory (* cpswordPropsTheory *)
     finite_mapTheory
     cpsword_to_wordTheory
     wordLangTheory wordPropsTheory;

local open backendTheory in end

val _ = new_theory "cpsword_to_wordProof";

val s = ``s:('a,'ffi) cpswordSem$state``

val _ = set_grammar_ancestry
  ["backend","cpswordLang","cpswordSem",
   "wordProps","cpsword_to_word","wordLang", "wordSem"]


val code_rel_def = Define `
  code_rel (s_code: (num # 'a cpswordLang$prog) num_map)
           (t_code: (num # 'a wordLang$prog) num_map) <=>
    domain t_code = domain s_code /\
    !n arg_count prog.
      (lookup n s_code = SOME (arg_count:num,prog)) ==>
      (lookup n t_code = SOME (arg_count,compile_prog prog))`


(*  [(("labProps", "good_dimindex_def"),
     (⊢ good_dimindex (:α) ⇔ dimindex (:α) = 32 ∨ dimindex (:α) = 64, Def))
*)

val state_rel_thm = Define `
  state_rel ^s (t:('a,'c,'ffi) wordSem$state) <=>
    (* I/O and clock are the same, GC is fixed, code is compiled *)
    (t.ffi = s.ffi) /\
    (t.clock = s.clock) /\
    code_rel s.code t.code /\
    (* every local is represented in wordLang *)
    (!n. IS_SOME (lookup n s.locals) ==>
         IS_SOME (lookup n t.locals))`


Theorem cpsword_compile_correct:
  !prog s res s' t.
    cpswordSem$evaluate (prog,s) = (res,s') /\ res <> (SOME Error) /\
    state_rel s t ==>
      ?t' res'.
        (evaluate ((compile_prog prog),t) = (res',t')) /\
        (res' = SOME NotEnoughSpace ==>
           t'.ffi.io_events ≼ s'.ffi.io_events) /\
        (res' <> SOME NotEnoughSpace ==>
         case res of
         | NONE => state_rel s' t' /\ (res' = NONE)
         | SOME (Return w) => state_rel s' t' /\ (res' = SOME (Result ARB w))
         | SOME (Exception w) => (t'.ffi = s'.ffi) /\
            (res' = SOME (Exception (mk_loc (jump_exc t)) w)) /\
            (jump_exc t <> NONE ==> state_rel s' t')
         | SOME (FinalFFI f) => (res' = SOME(FinalFFI f) /\ t'.ffi = s'.ffi)
         | SOME (TimeOut) => (res' = SOME TimeOut) /\ t'.ffi = s'.ffi)
Proof
  cheat
  (*fs [word_simpTheory.compile_exp_def,evaluate_simp_if,evaluate_Seq_assoc,
        evaluate_const_fp] *)
QED


val _ = export_theory();
