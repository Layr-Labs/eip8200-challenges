import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawRight2
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreRight2
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired80WordRound Paired80WordRotate Paired80WordBoolean StaggerCoreCommon
def input (memory : ByteArray) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory (.d) q right k, word memory (.k) q right k, word memory (.b) q right k, word memory (.c) q right k, word memory (.a) q right k, word memory (.e) q right k, word memory (.factor) q right k, word memory (.lower) q right k, word memory (.cache 140) q right k, word memory (.cache 190) q right k, word memory (.cache 310) q right k, word memory (.cache 350) q right k, word memory (.cache 500) q right k, word memory (.cache 230) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
theorem output_eq (memory : ByteArray) (q right : WordLane) (rho : List UInt256) :
    StaggerRawRight2.outputStack memory (input memory q right (UInt256.ofNat 1352829926)) rho =
      stack memory [ .d, .k, .c, .b, .e, .a, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500, .cache 230 ] (StaggerCoreModel.right2 memory q) (right) (UInt256.ofNat 1352829926) rho := by
  simp only [StaggerRawRight2.outputStack, input, stack, List.map_cons, List.map_nil,
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
def gasSteps (s : State) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 1062, stack := stack s.memory [ .d, .k, .b, .c, .a, .e, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500, .cache 230 ] q right (UInt256.ofNat 1352829926) rho}
      {s with pc := UInt256.ofNat 1093, stack := stack s.memory [ .d, .k, .c, .b, .e, .a, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500, .cache 230 ] (StaggerCoreModel.right2 s.memory q) (right) (UInt256.ofNat 1352829926) rho} := by
  have h := StaggerRawRight2.gasSteps s (input s.memory q right (UInt256.ofNat 1352829926)) rho hs hr ha hcode hfork hnp
  rw [output_eq] at h
  exact h
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreRight2
