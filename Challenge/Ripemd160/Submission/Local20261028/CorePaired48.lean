import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerModeSeven
import Challenge.Ripemd160.Submission.Local20261028.RawPaired48
import Challenge.Ripemd160.Submission.Local20261028.CoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePaired48
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation CoreCommon
def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.literal 23) q right k, word memory h4 (.cachedMessage 360) q right k, word memory h4 (.pair) q right k, word memory h4 (.upper) q right k, word memory h4 (.k) q right k, word memory h4 (.b) q right k, word memory h4 (.a) q right k, word memory h4 (.e) q right k, word memory h4 (.c) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 190) q right k, word memory h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerAlgorithm.step 48 (CoreModel.message memory 48) q

theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawPaired48.outputStack memory (input memory h4 q right (StaggerModeSeven.physicalKey 47)) rho =
      stack memory h4 [ .d, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval memory q) right (StaggerAlgorithm.physicalKey 48) rho := by
  have hkb : StaggerModeSeven.physicalKey 47 = UInt256.ofNat 45805601672572416830120737830960963807809187239029665 := by decide
  have hka : StaggerAlgorithm.physicalKey 48 = UInt256.ofNat 45805601672572416830120737830960963807809187780213980 := by decide
  have hm : StaggerAlgorithm.mode 48 = 3 := by decide
  have hl : Crypto.Ripemd160.s[48]! = 11 := by rfl
  have hr : Crypto.Ripemd160.sP[51]! = 11 := by rfl
  have hphysical : (UInt256.add (UInt256.ofNat 541184315) (UInt256.ofNat 45805601672572416830120737830960963807809187239029665)) = UInt256.ofNat 45805601672572416830120737830960963807809187780213980 := by decide
  try simp only [Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.RawPaired48.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, CoreCommon.word, eval, CoreModel.message, CoreModel.load, GeneralMessageLayout.addresses, StaggerTableLayout.pairIndices,
    StaggerAlgorithm.step, StaggerAdaptiveWord.usesAdaptive, StaggerAdaptiveWord.step, StaggerAdaptiveWord.t,
    StaggerAdaptiveWord.rotate, StaggerAdaptiveWord.compactWord, StaggerAdaptiveWord.gap, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true]
  try simp only [hphysical]
  try simp only [wordRotate, usesCompact, wordCompact, wordScale, wordShift, factorPlusWord, usesFusedExtra, wordFusedRotate, fusedCoefficientWord, fusedModulusWord]
  try simp
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
    StackRoundTrace.runInstrSeq RawPaired48.template
      {s with pc := UInt256.ofNat 3166, stack := stack s.memory h4 [ .d, .a, .cachedMessage 360, .pair, .upper, .k, .b, .literal 23, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerModeSeven.physicalKey 47) rho} =
      some {s with pc := UInt256.ofNat 3231, stack := stack s.memory h4 [ .d, .k, .cachedMessage 360, .pair, .upper, .e, .c, .literal 23, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 48) rho} := by
  have h := RawPaired48.run_actual s (UInt256.ofNat 3166)
    (input s.memory h4 q right (StaggerModeSeven.physicalKey 47)) rho hstack hrun hactive
  have hend : StackRoundTrace.pcAfter (UInt256.ofNat 3166) RawPaired48.template = UInt256.ofNat 3231 := by decide +kernel
  rw [hend, output_eq] at h
  exact h
#print axioms run
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.CorePaired48
