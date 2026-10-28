import Challenge.Ripemd160.Submission.Local20261028.PadModel
import Challenge.Ripemd160.Submission.Local20261028.PadRawLeft78
import Challenge.Ripemd160.Submission.Local20261028.PadCommon
import Challenge.Ripemd160.Submission.Local20261028.PadModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCoreLeft78
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation PadCommon
def input (n : UInt256) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word n h4 (.b) q right k, word n h4 (.d) q right k, word n h4 (.e) q right k, word n h4 (.ar) q right k, word n h4 (.cachedMessage 360) q right k, word n h4 (.pair) q right k, word n h4 (.upper) q right k, word n h4 (.er) q right k, word n h4 (.cr) q right k, word n h4 (.literal 23) q right k, word n h4 (.k) q right k, word n h4 (.c) q right k, word n h4 (.factor) q right k, word n h4 (.lower) q right k, word n h4 (.cache 140) q right k, word n h4 (.cache 350) q right k, word n h4 (.cache 310) q right k, word n h4 (.cache 190) q right k, word n h4 (.cache 500) q right k, UInt256.ofNat 0⟩
theorem output_eq (n : UInt256) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.e = q.a) (hsame2 : right.d = q.e) (hsame3 : right.b = q.c) :
    PadRawLeft78.outputStack n (input n h4 q right (UInt256.ofNat 2840853838)) rho =
      stack n h4 [ .d, .b, .c, .e, .a, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190 ] (PadModel.left78 n q) (right) (UInt256.ofNat 2840853838) (h4 :: rho) := by
  simp only [PadRawLeft78.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, PadCommon.word, PadValues.load, hsame, hsame2, hsame3,
    PadModel.initial, PadModel.pair, PadModel.pairWord, PadModel.left,
    PadModel.right0, PadModel.right1, PadModel.right2,
    PadModel.left77, PadModel.left78, PadModel.left79,
    StaggerScalarWord.step, StaggerScalarWord.t, StaggerScalarWord.sum, StaggerScalarWord.rawF,
    StaggerScalarWord.mask, wordShift, factorPlusWord, List.cons.injEq, and_true]
  all_goals try simp
  all_goals try simp only [PadCommon.add_comm, PadCommon.add_left_comm,
    PadCommon.add_assoc, PadCommon.mul_comm,
    PadCommon.land_comm, PadCommon.lor_comm, PadCommon.xor_comm,
    PadCommon.xor_left_comm, PadCommon.xor_assoc]
  all_goals first | rfl | trivial
#print axioms output_eq
theorem run (s : State) (n h4 : UInt256) (q right : WordLane) (rho : List UInt256) (hsame : right.e = q.a) (hsame2 : right.d = q.e) (hsame3 : right.b = q.c)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
 :
    StackRoundTrace.runInstrSeq PadRawLeft78.template {s with pc := UInt256.ofNat 7990, stack := stack n h4 [ .b, .d, .e, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (UInt256.ofNat 2840853838) rho} =
      some {s with pc := UInt256.ofNat 8014, stack := stack n h4 [ .d, .b, .c, .e, .a, .ar, .cachedMessage 360, .pair, .upper, .er, .cr, .literal 23, .k, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190 ] (PadModel.left78 n q) (right) (UInt256.ofNat 2840853838) (h4 :: rho)} := by
  have h := PadRawLeft78.run_actual s (UInt256.ofNat 7990) n (input n h4 q right (UInt256.ofNat 2840853838)) rho hs hr ha
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 7990) PadRawLeft78.template = UInt256.ofNat 8014 := by decide +kernel
  rw [hend] at h
  rw [output_eq n h4 q right rho hsame hsame2 hsame3] at h
  exact h
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCoreLeft78
