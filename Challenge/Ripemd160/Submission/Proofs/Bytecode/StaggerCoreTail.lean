import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreTail
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired80WordRound Paired80WordRotate Paired80WordBoolean StaggerCoreCommon
def input (memory : ByteArray) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory (.d) q right k, word memory (.b) q right k, word memory (.e) q right k, word memory (.a) q right k, word memory (.k) q right k, word memory (.c) q right k, word memory (.er) q right k, word memory (.cr) q right k, word memory (.ar) q right k, word memory (.dr) q right k, word memory (.br) q right k, word memory (.factor) q right k, word memory (.lower) q right k, word memory (.cache 140) q right k, word memory (.cache 190) q right k, word memory (.cache 310) q right k, word memory (.cache 350) q right k, word memory (.cache 500) q right k, word memory (.cache 230) q right k, UInt256.ofNat 0⟩
theorem output_eq (memory : ByteArray) (q right : WordLane) (rho : List UInt256) :
    StaggerRawTail.outputStack memory (input memory q right (UInt256.ofNat 2840853838)) rho =
      stack memory [  ] (q) (right) (UInt256.ofNat 0) rho := by
  simp only [StaggerRawTail.outputStack, input, stack, List.map_cons, List.map_nil,
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
theorem memory_eq (memory : ByteArray) (q right : WordLane) (k : UInt256) :
    StaggerRawTail.outputMemory memory (input memory q right k) =
      StaggerCoreModel.tailMemory memory q right := by
  simp (discharger := omega) only [StaggerRawTail.outputMemory, input, StaggerCoreCommon.word,
    StaggerCoreModel.tailMemory, StaggerCoreModel.rawHash, StaggerCoreModel.addResult,
    StaggerScalarWord.mask, PairedScheduleMemory.read_writeWord_disjoint]
  simp only [StaggerCoreCommon.add_comm, StaggerCoreCommon.add_left_comm,
    StaggerCoreCommon.add_assoc, StaggerCoreCommon.land_comm]
#print axioms memory_eq
def gasSteps (s : State) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4579, stack := stack s.memory [ .d, .b, .e, .a, .k, .c, .er, .cr, .ar, .dr, .br, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500, .cache 230 ] q right (UInt256.ofNat 2840853838) rho}
      {s with pc := UInt256.ofNat 4677, stack := stack s.memory [  ] (q) (right) (UInt256.ofNat 0) rho, memory := StaggerCoreModel.tailMemory s.memory q right} := by
  have h := StaggerRawTail.gasSteps s (input s.memory q right (UInt256.ofNat 2840853838)) rho hs hr ha hcode hfork hnp
  rw [output_eq, memory_eq] at h
  exact h
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreTail
