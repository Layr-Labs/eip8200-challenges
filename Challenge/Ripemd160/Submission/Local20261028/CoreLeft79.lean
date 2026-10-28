import Challenge.Ripemd160.Submission.Local20261028.RawLeft79
import Challenge.Ripemd160.Submission.Local20261028.CoreCommon
import Challenge.Ripemd160.Submission.Local20261028.CoreModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreLeft79
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation CoreCommon

def left79Raw (memory : ByteArray) (q : WordLane) : WordLane :=
  ⟨q.e, StaggerScalarWord.t false 4 6 (CoreModel.load memory 198) (UInt256.ofNat 2840853838) q, q.b, q.c, q.d⟩

def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.b) q right k, word memory h4 (.c) q right k, word memory h4 (.e) q right k, word memory h4 (.a) q right k, word memory h4 (.ar) q right k, word memory h4 (.cachedMessage 360) q right k, word memory h4 (.pair) q right k, word memory h4 (.upper) q right k, word memory h4 (.er) q right k, word memory h4 (.cr) q right k, word memory h4 (.literal 23) q right k, word memory h4 (.k) q right k, word memory h4 (.br) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 190) q right k⟩
theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.d = q.a) :
    RawLeft79.outputStack memory (input memory h4 q right (UInt256.ofNat 2840853838)) (h4 :: rho) =
      stack memory h4 [ .b, .c, .d, .a, .dr, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .e, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (left79Raw memory q) (right) (UInt256.ofNat 2840853838) rho := by
  simp only [RawLeft79.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, CoreCommon.word, CoreModel.load, GeneralMessageLayout.addresses, hsame,
    CoreModel.initial, CoreModel.pair, CoreModel.pairWord, CoreModel.left,
    CoreModel.right0, CoreModel.right1, CoreModel.right2,
    CoreModel.left77, CoreModel.left78, left79Raw,
    StaggerScalarWord.step, StaggerScalarWord.t, StaggerScalarWord.sum, StaggerScalarWord.rawF,
    StaggerScalarWord.mask, wordShift, factorPlusWord, List.cons.injEq, and_true]
  all_goals try simp
  all_goals try simp only [CoreCommon.add_comm, CoreCommon.add_left_comm,
    CoreCommon.add_assoc, CoreCommon.mul_comm,
    CoreCommon.land_comm, CoreCommon.lor_comm, CoreCommon.xor_comm,
    CoreCommon.xor_left_comm, CoreCommon.xor_assoc]
  all_goals first | rfl | trivial
#print axioms output_eq
theorem run (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.d = q.a)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
 :
    StackRoundTrace.runInstrSeq RawLeft79.template {s with pc := UInt256.ofNat 4499, stack := stack s.memory h4 [ .d, .b, .c, .e, .a, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190 ] q right (UInt256.ofNat 2840853838) (h4 :: rho)} =
      some {s with pc := UInt256.ofNat 4523, stack := stack s.memory h4 [ .b, .c, .d, .a, .dr, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .e, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (left79Raw s.memory q) (right) (UInt256.ofNat 2840853838) rho} := by
  have h := RawLeft79.run_actual s (UInt256.ofNat 4499) (input s.memory h4 q right (UInt256.ofNat 2840853838)) (h4 :: rho) (by simp only [List.length_cons]; omega) hr ha
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 4499) RawLeft79.template = UInt256.ofNat 4523 := by decide +kernel
  rw [hend] at h
  rw [output_eq s.memory h4 q right rho hsame] at h
  exact h
#print axioms run

def epilogueRaw (memory : ByteArray) (q : WordLane) : WordLane :=
  left79Raw memory (CoreModel.left78 memory (CoreModel.left77 memory (CoreModel.left q)))

theorem left79Raw_a (memory : ByteArray) (X : WordLane) : (left79Raw memory X).a = (CoreModel.left79 memory X).a := by
  dsimp only [left79Raw, CoreModel.left79, StaggerScalarWord.step]
theorem left79Raw_b (memory : ByteArray) (X : WordLane) : (left79Raw memory X).b = (CoreModel.left79 memory X).b := by
  dsimp only [left79Raw, CoreModel.left79, StaggerScalarWord.step]
theorem left79Raw_c (memory : ByteArray) (X : WordLane) : (left79Raw memory X).c = (CoreModel.left79 memory X).c := by
  dsimp only [left79Raw, CoreModel.left79, StaggerScalarWord.step]
theorem left79Raw_e (memory : ByteArray) (X : WordLane) : (left79Raw memory X).e = (CoreModel.left79 memory X).e := by
  dsimp only [left79Raw, CoreModel.left79, StaggerScalarWord.step]
theorem left79Raw_d_shift (memory : ByteArray) (X : WordLane) : wordShift (left79Raw memory X).d 23 = (CoreModel.left79 memory X).d := by
  dsimp only [left79Raw, CoreModel.left79, StaggerScalarWord.step]
  rw [if_neg Bool.false_ne_true]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CoreLeft79
