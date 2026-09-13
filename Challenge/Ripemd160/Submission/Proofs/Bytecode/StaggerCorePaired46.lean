import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedMultiplierRescale
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerModeSeven
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired46
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired46
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.literal 28) q right k, word memory h4 (.cachedMessage 360) q right k, word memory h4 (.pair) q right k, word memory h4 (.upper) q right k, word memory h4 (.e) q right k, word memory h4 (.b) q right k, word memory h4 (.a) q right k, word memory h4 (.k) q right k, word memory h4 (.c) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 190) q right k, word memory h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerModeSeven.step 46 (MachineState.readWord memory 702) q

theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    StaggerRawPaired46.outputStack memory (input memory h4 q right (StaggerModeSeven.physicalKey 45)) rho =
      stack memory h4 [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .e, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval memory q) right (StaggerModeSeven.physicalKey 46) rho := by
  have hkb : StaggerModeSeven.physicalKey 45 = UInt256.ofNat 45805601672572416830120737830960963807809187239029665 := by decide
  have hka : StaggerModeSeven.physicalKey 46 = UInt256.ofNat 45805601672572416830120737830960963807809187239029665 := by decide
  have hm : StaggerAlgorithm.mode 46 = 7 := by decide
  have hl : Crypto.Ripemd160.s[46]! = 7 := by rfl
  have hr : Crypto.Ripemd160.sP[49]! = 5 := by rfl
  have hrescale (x y : UInt256) :
      UInt256.land pairWord (UInt256.add y (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 10141204804187018453417038184450) x) (UInt256.ofNat 26))) =
      UInt256.land pairWord (UInt256.add y (UInt256.shiftRight (UInt256.mul (UInt256.ofNat 20282409608374036906834076368900) x) (UInt256.ofNat 27))) := by
    exact (PackedMultiplierRescale.at_shift27 x y).symm
  simp only [StaggerRawPaired46.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, StaggerCoreCommon.word, eval,
    StaggerModeSeven.step, StaggerModeSeven.enabled, if_pos (by omega),
    StaggerModeSeven.sum, StaggerModeSeven.raw, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true, hrescale]
  simp only [wordRotate, usesCompact, wordCompact, wordScale, wordShift]
  simp
  all_goals try simp only [upperWord, lowerWord, and_true, true_and]
  all_goals simp only [StaggerCoreCommon.add_comm, StaggerCoreCommon.add_left_comm,
    StaggerCoreCommon.add_assoc, StaggerCoreCommon.mul_comm, StaggerCoreCommon.mul_one,
    StaggerCoreCommon.land_comm, StaggerCoreCommon.lor_comm, StaggerCoreCommon.xor_comm,
    StaggerCoreCommon.xor_left_comm, StaggerCoreCommon.xor_assoc, and_true, true_and]
  all_goals first | rfl | trivial
#print axioms output_eq

def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 3114, stack := stack s.memory h4 [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .a, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] q right (StaggerModeSeven.physicalKey 45) rho}
      {s with pc := UInt256.ofNat 3172, stack := stack s.memory h4 [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .e, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (eval s.memory q) right (StaggerModeSeven.physicalKey 46) rho} := by
  have g := StaggerRawPaired46.gasSteps s (input s.memory h4 q right (StaggerModeSeven.physicalKey 45))
    rho hstack hrun hactive hcode hfork hnp
  rw [output_eq] at g
  exact g
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired46
