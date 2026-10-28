import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMultiplierRescale
import Challenge.Ripemd160.Submission.Local20261028.PadRaw33
import Challenge.Ripemd160.Submission.Local20261028.PadCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCore33
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation PadCommon
def input (n : UInt256) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word n h4 (.d) q right k, word n h4 (.cache 350) q right k, word n h4 (.factor) q right k, word n h4 (.cache 350) q right k, word n h4 (.e) q right k, word n h4 (.cachedMessage 360) q right k, word n h4 (.pair) q right k, word n h4 (.upper) q right k, word n h4 (.k) q right k, word n h4 (.c) q right k, word n h4 (.literal 23) q right k, word n h4 (.a) q right k, word n h4 (.b) q right k, word n h4 (.factor) q right k, word n h4 (.lower) q right k, word n h4 (.cache 140) q right k, word n h4 (.cache 350) q right k, word n h4 (.cache 310) q right k, word n h4 (.cache 190) q right k, word n h4 (.cache 500) q right k⟩
def eval (n : UInt256) (q : WordLane) : WordLane :=
  StaggerAlgorithm.step 33 (PadValues.load n 306) q

theorem output_eq (n : UInt256) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRaw33.outputStack n (input n h4 q right (StaggerAlgorithm.physicalKey 32)) rho =
      stack n h4 [ .d, .factor, .cache 350, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval n q) right (StaggerAlgorithm.physicalKey 33) rho := by
  have hkb : StaggerAlgorithm.physicalKey 32 = UInt256.ofNat 136726760529788758926252426176837954510549114783656865 := by decide
  have hka : StaggerAlgorithm.physicalKey 33 = UInt256.ofNat 136726760529788758926252426176837954510549114783656865 := by decide
  have hm : StaggerAlgorithm.mode 33 = 2 := by decide
  have hl : Crypto.Ripemd160.s[33]! = 13 := by rfl
  have hr : Crypto.Ripemd160.sP[36]! = 8 := by rfl
  have hrescale (x y : UInt256) :
      UInt256.land pairWord (UInt256.add y (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 10141204804187018453477167726608) x) (UInt256.ofNat 23))) =
      UInt256.land pairWord (UInt256.add y (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 20282409608374036906954335453216) x) (UInt256.ofNat 24))) := by
    exact (PackedMultiplierRescale.at_shift24 x y).symm
  try simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadRaw33.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, PadCommon.word, eval, PadValues.load,
    StaggerAlgorithm.step, StaggerAdaptiveWord.usesAdaptive, StaggerAdaptiveWord.step, StaggerAdaptiveWord.t,
    StaggerAdaptiveWord.rotate, StaggerAdaptiveWord.compactWord, StaggerAdaptiveWord.gap, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true, hrescale]
  try simp only [wordRotate, usesCompact, wordCompact, wordScale, wordShift, factorPlusWord, usesFusedExtra, wordFusedRotate, fusedCoefficientWord, fusedModulusWord]
  try simp
  all_goals try simp only [upperWord, lowerWord, and_true, true_and]
  all_goals simp only [PadCommon.add_comm, PadCommon.add_left_comm,
    PadCommon.add_assoc, PadCommon.mul_comm, PadCommon.mul_one,
    PadCommon.land_comm, PadCommon.lor_comm, PadCommon.xor_comm,
    PadCommon.xor_left_comm, PadCommon.xor_assoc, RawExpressionAC.mulMod_comm, and_true, true_and]
  all_goals first | rfl | trivial
#print axioms output_eq

theorem run (s : State) (n h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running) (hactive : 34 ≤ s.activeWords.toNat)
    (hcal : UInt256.ofNat s.executionEnv.calldata.size = n)
    (hmem : MachineState.readWord s.memory 0 = PadValues.load n 162) :
    StackRoundTrace.runInstrSeq PadRaw33.template
      {s with pc := UInt256.ofNat 6207, stack := stack n h4 [ .d, .cache 350, .factor, .cache 350, .e, .cachedMessage 360, .pair, .upper, .k, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerAlgorithm.physicalKey 32) rho} =
      some {s with pc := UInt256.ofNat 6248, stack := stack n h4 [ .d, .factor, .cache 350, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval n q) right (StaggerAlgorithm.physicalKey 33) rho} := by
  have h := PadRaw33.run_actual s (UInt256.ofNat 6207) n
    (input n h4 q right (StaggerAlgorithm.physicalKey 32)) rho hstack hrun hactive hcal hmem
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 6207) PadRaw33.template = UInt256.ofNat 6248 := by decide +kernel
  rw [hend, output_eq] at h
  exact h
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadCore33
