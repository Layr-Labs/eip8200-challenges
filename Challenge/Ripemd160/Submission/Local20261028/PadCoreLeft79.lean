import Challenge.Ripemd160.Submission.Local20261028.PadModel
import Challenge.Ripemd160.Submission.Local20261028.PadRawLeft79
import Challenge.Ripemd160.Submission.Local20261028.PadCommon
import Challenge.Ripemd160.Submission.Local20261028.PadModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCoreLeft79
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation PadCommon

def left79Raw (n : UInt256) (q : WordLane) : WordLane :=
  ⟨q.e, StaggerScalarWord.t false 4 6 (PadValues.load n 198) (UInt256.ofNat 2840853838) q, q.b, q.c, q.d⟩

def input (n : UInt256) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word n h4 (.d) q right k, word n h4 (.b) q right k, word n h4 (.c) q right k, word n h4 (.e) q right k, word n h4 (.a) q right k, word n h4 (.ar) q right k, word n h4 (.cachedMessage 360) q right k, word n h4 (.pair) q right k, word n h4 (.upper) q right k, word n h4 (.er) q right k, word n h4 (.cr) q right k, word n h4 (.literal 23) q right k, word n h4 (.k) q right k, word n h4 (.br) q right k, word n h4 (.factor) q right k, word n h4 (.lower) q right k, word n h4 (.cache 140) q right k, word n h4 (.cache 350) q right k, word n h4 (.cache 310) q right k, word n h4 (.cache 190) q right k⟩
theorem output_eq (n : UInt256) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.d = q.a) :
    PadRawLeft79.outputStack n (input n h4 q right (UInt256.ofNat 2840853838)) (h4 :: rho) =
      stack n h4 [ .b, .c, .d, .a, .dr, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .e, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (left79Raw n q) (right) (UInt256.ofNat 2840853838) rho := by
  simp only [PadRawLeft79.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, PadCommon.word, PadValues.load, hsame,
    PadModel.initial, PadModel.pair, PadModel.pairWord, PadModel.left,
    PadModel.right0, PadModel.right1, PadModel.right2,
    PadModel.left77, PadModel.left78, left79Raw,
    StaggerScalarWord.step, StaggerScalarWord.t, StaggerScalarWord.sum, StaggerScalarWord.rawF,
    StaggerScalarWord.mask, wordShift, factorPlusWord, List.cons.injEq, and_true]
  all_goals try simp
  all_goals try simp only [PadCommon.add_comm, PadCommon.add_left_comm,
    PadCommon.add_assoc, PadCommon.mul_comm,
    PadCommon.land_comm, PadCommon.lor_comm, PadCommon.xor_comm,
    PadCommon.xor_left_comm, PadCommon.xor_assoc]
  all_goals first | rfl | trivial
#print axioms output_eq
theorem run (s : State) (n h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.d = q.a)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
 :
    StackRoundTrace.runInstrSeq PadRawLeft79.template {s with pc := UInt256.ofNat 8014, stack := stack n h4 [ .d, .b, .c, .e, .a, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190 ] q right (UInt256.ofNat 2840853838) (h4 :: rho)} =
      some {s with pc := UInt256.ofNat 8033, stack := stack n h4 [ .b, .c, .d, .a, .dr, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .e, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (left79Raw n q) (right) (UInt256.ofNat 2840853838) rho} := by
  have h := PadRawLeft79.run_actual s (UInt256.ofNat 8014) n (input n h4 q right (UInt256.ofNat 2840853838)) (h4 :: rho) (by simp only [List.length_cons]; omega) hr ha
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 8014) PadRawLeft79.template = UInt256.ofNat 8033 := by decide +kernel
  rw [hend] at h
  rw [output_eq n h4 q right rho hsame] at h
  exact h
#print axioms run

def epilogueRaw (n : UInt256) (q : WordLane) : WordLane :=
  left79Raw n (PadModel.left78 n (PadModel.left77 n (PadModel.left q)))

theorem left79Raw_a (n : UInt256) (X : WordLane) : (left79Raw n X).a = (PadModel.left79 n X).a := by
  dsimp only [left79Raw, PadModel.left79, StaggerScalarWord.step]
theorem left79Raw_b (n : UInt256) (X : WordLane) : (left79Raw n X).b = (PadModel.left79 n X).b := by
  dsimp only [left79Raw, PadModel.left79, StaggerScalarWord.step]
theorem left79Raw_c (n : UInt256) (X : WordLane) : (left79Raw n X).c = (PadModel.left79 n X).c := by
  dsimp only [left79Raw, PadModel.left79, StaggerScalarWord.step]
theorem left79Raw_e (n : UInt256) (X : WordLane) : (left79Raw n X).e = (PadModel.left79 n X).e := by
  dsimp only [left79Raw, PadModel.left79, StaggerScalarWord.step]
theorem left79Raw_d_shift (n : UInt256) (X : WordLane) : wordShift (left79Raw n X).d 23 = (PadModel.left79 n X).d := by
  dsimp only [left79Raw, PadModel.left79, StaggerScalarWord.step]
  rw [if_neg Bool.false_ne_true]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCoreLeft79
