import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerRawPaired63
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired63
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge
open Paired80WordRound Paired80WordRotate Paired80WordBoolean StaggerCoreCommon
def input (memory : ByteArray) (q right : WordLane) (k : UInt256) : StaggerRaw.Input :=
  ⟨word memory (.d) q right k, word memory (.pair) q right k, word memory (.upper) q right k, word memory (.k) q right k, word memory (.c) q right k, word memory (.a) q right k, word memory (.e) q right k, word memory (.b) q right k, word memory (.factor) q right k, word memory (.lower) q right k, word memory (.cache 140) q right k, word memory (.cache 190) q right k, word memory (.cache 310) q right k, word memory (.cache 350) q right k, word memory (.cache 500) q right k, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0, UInt256.ofNat 0⟩
def eval (memory : ByteArray) (q : WordLane) : WordLane :=
  StaggerAlgorithm.step 63 (MachineState.readWord memory 180) q

theorem output_eq (memory : ByteArray) (q right : WordLane) (rho : List UInt256) :
    StaggerRawPaired63.outputStack memory (input memory q right (StaggerAlgorithm.physicalKey 62)) rho =
      stack memory [ .d, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (eval memory q) right (StaggerAlgorithm.physicalKey 63) rho := by
  have hkb : StaggerAlgorithm.physicalKey 62 = UInt256.ofNat 2400959708 := by decide
  have hka : StaggerAlgorithm.physicalKey 63 = UInt256.ofNat 2400959708 := by decide
  have hm : StaggerAlgorithm.mode 63 = 8 := by decide
  have hl : Crypto.Ripemd160.s[63]! = 12 := by rfl
  have hr : Crypto.Ripemd160.sP[66]! = 12 := by rfl
  simp only [StaggerRawPaired63.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, StaggerCoreCommon.word, eval,
    StaggerAlgorithm.step, hkb, hka, hm, hl, hr,
    upperWord, lowerWord, StaggerWord.step, StaggerWord.t, StaggerWord.sum,
    StaggerWord.raw, StaggerWord.selector, StaggerWord.key, StaggerBoolean.selector,
    List.cons.injEq, and_true]
  simp only [wordRotate, wordScale, wordShift]
  simp
  all_goals try simp only [upperWord, lowerWord, and_true, true_and]
  all_goals simp only [StaggerCoreCommon.add_comm, StaggerCoreCommon.add_left_comm,
    StaggerCoreCommon.add_assoc, StaggerCoreCommon.mul_comm, StaggerCoreCommon.mul_one,
    StaggerCoreCommon.land_comm, StaggerCoreCommon.lor_comm, StaggerCoreCommon.xor_comm,
    StaggerCoreCommon.xor_left_comm, StaggerCoreCommon.xor_assoc, and_true, true_and]
  all_goals first | rfl | trivial
#print axioms output_eq

def gasSteps (s : State) (q right : WordLane) (rho : List UInt256)
    (hstack : rho.length ≤ 900) (hrun : s.halt = .Running)
    (hactive : 34 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 3903, stack := stack s.memory [ .d, .pair, .upper, .k, .c, .a, .e, .b, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] q right (StaggerAlgorithm.physicalKey 62) rho}
      {s with pc := UInt256.ofNat 3943, stack := stack s.memory [ .d, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 190, .cache 310, .cache 350, .cache 500 ] (eval s.memory q) right (StaggerAlgorithm.physicalKey 63) rho} := by
  have g := StaggerRawPaired63.gasSteps s (input s.memory q right (StaggerAlgorithm.physicalKey 62))
    rho hstack hrun hactive hcode hfork hnp
  rw [output_eq] at g
  exact g
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePaired63
