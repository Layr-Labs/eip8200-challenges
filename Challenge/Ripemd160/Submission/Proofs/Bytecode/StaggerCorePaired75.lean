import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTerminal75
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired75
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired75
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired144WordRound Paired144WordRotation StaggerCoreCommon
def input (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory h4 (.d) q right k, word memory h4 (.pair) q right k, word memory h4 (.upper) q right k, word memory h4 (.e) q right k, word memory h4 (.c) q right k, word memory h4 (.a) q right k, word memory h4 (.k) q right k, word memory h4 (.b) q right k, word memory h4 (.factor) q right k, word memory h4 (.lower) q right k, word memory h4 (.cache 140) q right k, word memory h4 (.cache 190) q right k, word memory h4 (.cache 310) q right k, word memory h4 (.cache 350) q right k, word memory h4 (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerTerminal75.step 75 (MachineState.readWord memory 738) q

theorem output_eq (memory : ByteArray) (h4 : UInt256) (q right : WordLane) (rho : List UInt256) :
    StaggerRawPaired75.outputStack memory (input memory h4 q right (StaggerAlgorithm.physicalKey 74)) rho =
      stack memory h4 [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (eval memory q) right (StaggerAlgorithm.physicalKey 75) rho := by
  have hkb : StaggerAlgorithm.physicalKey 74 = UInt256.ofNat 2840853838 := by decide
  have hka : StaggerAlgorithm.physicalKey 75 = UInt256.ofNat 2840853838 := by decide
  have hm : StaggerAlgorithm.mode 75 = 4 := by decide
  have hl : Crypto.Ripemd160.s[75]! = 14 := by rfl
  have hr : Crypto.Ripemd160.sP[78]! = 11 := by rfl
  simp only [StaggerRawPaired75.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, StaggerCoreCommon.word, eval,
    StaggerTerminal75.step, if_pos rfl, StaggerAlgorithm.step, hkb, hka, hm, hl, hr,
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
    GasSteps {s with pc := UInt256.ofNat 4480, stack := stack s.memory h4 [ .d, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] q right (StaggerAlgorithm.physicalKey 74) rho}
      {s with pc := UInt256.ofNat 4522, stack := stack s.memory h4 [ .d, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 75) rho} := by
  have g := StaggerRawPaired75.gasSteps s (input s.memory h4 q right (StaggerAlgorithm.physicalKey 74))
    rho hstack hrun hactive hcode hfork hnp
  rw [output_eq] at g
  exact g
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired75
