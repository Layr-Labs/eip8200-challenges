import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired7
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired7
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.pair) q right k, word memory h4 (.upper) q right k, word memory h4 (.a) q right k, word memory h4 (.c) q right k, word memory h4 (.k) q right k, word memory h4 (.e) q right k, word memory h4 (.b) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 190) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerAlgorithm.step 7 (MachineState.readWord memory 612) q

theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    StaggerRawPaired7.outputStack memory (input memory h4 q right (StaggerAlgorithm.physicalKey 6)) rho =
      stack memory h4 [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (eval memory q) right (StaggerAlgorithm.physicalKey 7) rho := by
  have hkb : StaggerAlgorithm.physicalKey 6 = UInt256.ofNat 30169115476673038213297653277143730720156734734729216 := by decide
  have hka : StaggerAlgorithm.physicalKey 7 = UInt256.ofNat 30169115476673038213297653277143730720156734734729216 := by decide
  have hm : StaggerAlgorithm.mode 7 = 0 := by decide
  have hl : Crypto.Ripemd160.s[7]! = 9 := by rfl
  have hr : Crypto.Ripemd160.sP[10]! = 8 := by rfl
  simp only [StaggerRawPaired7.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, StaggerCoreCommon.word, eval,
    StaggerAlgorithm.step, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true]
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
    GasSteps {s with pc := UInt256.ofNat 1464, stack := stack s.memory h4 [ .d, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] q right (StaggerAlgorithm.physicalKey 6) rho}
      {s with pc := UInt256.ofNat 1507, stack := stack s.memory h4 [ .d, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 7) rho} := by
  have g := StaggerRawPaired7.gasSteps s (input s.memory h4 q right (StaggerAlgorithm.physicalKey 6))
    rho hstack hrun hactive hcode hfork hnp
  rw [output_eq] at g
  exact g
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired7
