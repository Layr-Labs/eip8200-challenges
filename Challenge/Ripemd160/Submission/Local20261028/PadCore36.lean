import Challenge.Ripemd160.Submission.Local20261028.PadRaw36
import Challenge.Ripemd160.Submission.Local20261028.PadCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCore36
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation PadCommon
def input (n : UInt256) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word n h4 (.d) q right k, word n h4 (.literal 23) q right k, word n h4 (.cachedMessage 360) q right k, word n h4 (.pair) q right k, word n h4 (.upper) q right k, word n h4 (.k) q right k, word n h4 (.b) q right k, word n h4 (.a) q right k, word n h4 (.e) q right k, word n h4 (.c) q right k, word n h4 (.factor) q right k, word n h4 (.lower) q right k, word n h4 (.cache 140) q right k, word n h4 (.cache 350) q right k, word n h4 (.cache 310) q right k, word n h4 (.cache 190) q right k, word n h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (n : UInt256) (q : WordLane) : WordLane :=
  StaggerAlgorithm.step 36 (PadValues.load n 828) q

theorem output_eq (n : UInt256) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRaw36.outputStack n (input n h4 q right (StaggerAlgorithm.physicalKey 35)) rho =
      stack n h4 [ .d, .cache 310, .cache 140, .e, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval n q) right (StaggerAlgorithm.physicalKey 36) rho := by
  have hkb : StaggerAlgorithm.physicalKey 35 = UInt256.ofNat 136726760529788758926252426176837954510549114783656865 := by decide
  have hka : StaggerAlgorithm.physicalKey 36 = UInt256.ofNat 136726760529788758926252426176837954510549114783656865 := by decide
  have hm : StaggerAlgorithm.mode 36 = 2 := by decide
  have hl : Crypto.Ripemd160.s[36]! = 14 := by rfl
  have hr : Crypto.Ripemd160.sP[39]! = 14 := by rfl
  try simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRaw36.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, PadCommon.word, eval, PadValues.load,
    StaggerAlgorithm.step, StaggerAdaptiveWord.usesAdaptive, StaggerAdaptiveWord.step, StaggerAdaptiveWord.t,
    StaggerAdaptiveWord.rotate, StaggerAdaptiveWord.compactWord, StaggerAdaptiveWord.gap, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true]
  try simp only [wordRotate, usesCompact, wordCompact, wordScale, wordShift, factorPlusWord, usesFusedExtra, wordFusedRotate, fusedCoefficientWord, fusedModulusWord]
  try simp
  all_goals try simp only [upperWord, lowerWord, and_true, true_and]
  all_goals simp only [PadCommon.add_comm, PadCommon.add_left_comm,
    PadCommon.add_assoc, PadCommon.mul_comm, PadCommon.mul_one,
    PadCommon.land_comm, PadCommon.lor_comm, PadCommon.xor_comm,
    PadCommon.xor_left_comm, PadCommon.xor_assoc, and_true, true_and]
  all_goals first | rfl | trivial
#print axioms output_eq

theorem run (s : State) (n h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162) :
    StackRoundTrace.runInstrSeq PadRaw36.template
      {s with pc := UInt256.ofNat 6306, stack := stack n h4 [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 35) rho} =
      some {s with pc := UInt256.ofNat 6337, stack := stack n h4 [ .d, .cache 310, .cache 140, .e, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval n q) right (StaggerAlgorithm.physicalKey 36) rho} := by
  have h := PadRaw36.run_actual s (UInt256.ofNat 6306) n
    (input n h4 q right (StaggerAlgorithm.physicalKey 35)) rho hstack hrun hactive hcal hmem
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 6306) PadRaw36.template = UInt256.ofNat 6337 := by decide +kernel
  rw [hend, output_eq] at h
  exact h
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCore36
