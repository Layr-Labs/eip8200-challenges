import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawRight1
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreRight1
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.k) q right k, word memory h4 (.c) q right k, word memory h4 (.b) q right k, word memory h4 (.e) q right k, word memory h4 (.a) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 190) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    StaggerRawRight1.outputStack memory (input memory h4 q right (UInt256.ofNat 1352829926)) rho =
      stack memory h4 [ .d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (StaggerCoreModel.right1 memory q) (right) (UInt256.ofNat 1352829926) rho := by
  simp only [StaggerRawRight1.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, StaggerCoreCommon.word,
    StaggerCoreModel.initial, StaggerCoreModel.pair, StaggerCoreModel.pairWord, StaggerCoreModel.left,
    StaggerCoreModel.right0, StaggerCoreModel.right1, StaggerCoreModel.right2,
    StaggerCoreModel.left77, StaggerCoreModel.left78, StaggerCoreModel.left79,
    StaggerScalarWord.step, StaggerScalarWord.t, StaggerScalarWord.sum, StaggerScalarWord.rawF,
    StaggerScalarWord.mask, wordShift, List.cons.injEq, and_true]
  all_goals try simp
  all_goals try simp only [StaggerCoreCommon.add_comm, StaggerCoreCommon.add_left_comm,
    StaggerCoreCommon.add_assoc, StaggerCoreCommon.mul_comm,
    StaggerCoreCommon.land_comm, StaggerCoreCommon.lor_comm, StaggerCoreCommon.xor_comm,
    StaggerCoreCommon.xor_left_comm, StaggerCoreCommon.xor_assoc]
  all_goals first | rfl | trivial
#print axioms output_eq
def gasSteps (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1041, stack := stack s.memory h4 [ .d, .k, .c, .b, .e, .a, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] q right (UInt256.ofNat 1352829926) rho}
      {s with pc := UInt256.ofNat 1073, stack := stack s.memory h4 [ .d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (StaggerCoreModel.right1 s.memory q) (right) (UInt256.ofNat 1352829926) rho} := by
  have h := StaggerRawRight1.gasSteps s (input s.memory h4 q right (UInt256.ofNat 1352829926)) rho hs hr ha hcode hfork hnp
  rw [output_eq] at h
  exact h
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreRight1
