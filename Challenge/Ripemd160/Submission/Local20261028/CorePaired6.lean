import Challenge.Ripemd160.Submission.Local20261028.RawPaired6
import Challenge.Ripemd160.Submission.Local20261028.CoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePaired6
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation CoreCommon
def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.literal 23) q right k, word memory h4 (.cachedMessage 360) q right k, word memory h4 (.pair) q right k, word memory h4 (.upper) q right k, word memory h4 (.e) q right k, word memory h4 (.b) q right k, word memory h4 (.k) q right k, word memory h4 (.a) q right k, word memory h4 (.c) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 190) q right k, word memory h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerAlgorithm.step 6 (CoreModel.message memory 6) q

theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawPaired6.outputStack memory (input memory h4 q right (StaggerAlgorithm.physicalKey 5)) rho =
      stack memory h4 [ .d, .factor, .cache 350, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval memory q) right (StaggerAlgorithm.physicalKey 6) rho := by
  have hkb : StaggerAlgorithm.physicalKey 5 = UInt256.ofNat 30169115476673038213297653277143730720156734734729216 := by decide
  have hka : StaggerAlgorithm.physicalKey 6 = UInt256.ofNat 30169115476673038213297653277143730720156734734729216 := by decide
  have hm : StaggerAlgorithm.mode 6 = 0 := by decide
  have hl : Crypto.Ripemd160.s[6]! = 7 := by rfl
  have hr : Crypto.Ripemd160.sP[9]! = 7 := by rfl
  simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawPaired6.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, CoreCommon.word, eval, CoreModel.message, CoreModel.load, GeneralMessageLayout.addresses, StaggerTableLayout.pairIndices,
    StaggerAlgorithm.step, StaggerAdaptiveWord.usesAdaptive, StaggerAdaptiveWord.step, StaggerAdaptiveWord.t,
    StaggerAdaptiveWord.rotate, StaggerAdaptiveWord.compactWord, StaggerAdaptiveWord.gap, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true]
  simp only [wordRotate, usesCompact, wordCompact, wordScale, wordShift, factorPlusWord, usesFusedExtra, wordFusedRotate, fusedCoefficientWord, fusedModulusWord]
  simp
  all_goals try simp only [upperWord, lowerWord, and_true, true_and]
  all_goals simp only [CoreCommon.add_comm, CoreCommon.add_left_comm,
    CoreCommon.add_assoc, CoreCommon.mul_comm, CoreCommon.mul_one,
    CoreCommon.land_comm, CoreCommon.lor_comm, CoreCommon.xor_comm,
    CoreCommon.xor_left_comm, CoreCommon.xor_assoc, and_true, true_and]
  all_goals first | rfl | trivial
#print axioms output_eq

theorem run (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat) :
    StackRoundTrace.runInstrSeq RawPaired6.template
      {s with pc := UInt256.ofNat 1261, stack := stack s.memory h4 [ .d, .literal 23, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 5) rho} =
      some {s with pc := UInt256.ofNat 1301, stack := stack s.memory h4 [ .d, .factor, .cache 350, .e, .literal 23, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 6) rho} := by
  have h := RawPaired6.run_actual s (UInt256.ofNat 1261)
    (input s.memory h4 q right (StaggerAlgorithm.physicalKey 5)) rho hstack hrun hactive
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 1261) RawPaired6.template = UInt256.ofNat 1301 := by decide +kernel
  rw [hend, output_eq] at h
  exact h
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePaired6
