import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80RawRound53
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreRound53
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge Paired80WordRound Paired80WordRotate Paired80WordBoolean
open Table80CoreCommon
def input (q : WordLane) (k : UInt256) : Table80Raw.Input :=
  ⟨word .d q k, word .e q k, word .c q k, word .b q k, word .k q k, word .a q k, word .factor q k, word .pair q k, word .upper q k, word .lower q k⟩
def eval (message k : UInt256) (q : WordLane) : WordLane := wordStep 3 15 14 message k q
def nextKey (k : UInt256) : UInt256 := k
theorem output_eq (memory : ByteArray) (q : WordLane) (k : UInt256) (rho : List UInt256) :
    Table80RawRound53.outputStack memory (input q k) rho =
      stack [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] (eval (MachineState.readWord memory 80) k q) (nextKey k) rho := by
  simp only [Table80RawRound53.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Table80CoreCommon.word, eval, nextKey,
    wordStep, wordT, wordSum, Paired80WordGroupTwoHoist.rawWordStep2,
    Paired80WordGroupTwoHoist.hoistedT, Paired80WordGroupTwoHoist.hoistedSum,
    Paired80WordGroupTwoHoist.hoistedBoolean, Paired80FinalWord.rawStep,
    boolean_zero, boolean_one, boolean_three, boolean_four,
    PairedLaneBooleanFactoring.factoredWord, PairedLaneBooleanSynthesis.oneWord,
    PairedLaneBooleanSynthesis.threeWord, List.cons.injEq, and_true]
  simp only [wordRotate, wordScale, wordShift]
  simp
  all_goals simp only [Table80CoreCommon.add_comm, Table80CoreCommon.add_left_comm,
    Table80CoreCommon.add_assoc, Table80CoreCommon.mul_comm, Table80CoreCommon.mul_one,
    Table80CoreCommon.land_comm, Table80CoreCommon.lor_comm,
    Table80CoreCommon.xor_comm, Table80CoreCommon.xor_left_comm, Table80CoreCommon.xor_assoc]
  all_goals trivial
#print axioms output_eq

 theorem nextKey_physical : nextKey (Paired80Algorithm.physicalKey 53) =
     Paired80Algorithm.physicalKey 54 := by decide

 theorem eval_physical (message : UInt256) (q : WordLane) :
     eval message (Paired80Algorithm.physicalKey 53) q = Paired80Algorithm.step 53 message q := by rfl

 def gasSteps (s : State) (q : WordLane) (k : UInt256) (rho : List UInt256)
     (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
     (hactive : 34 ≤ s.activeWords.toNat)
     (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
     (hfork : s.fork = .Osaka)
     (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
       s.executionEnv.fork s.executionEnv.codeAddr = false) :
     Challenge.EvmProof.GasSteps {s with pc := UInt256.ofNat 3413, stack := stack [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] q k rho}
       {s with pc := UInt256.ofNat 3456, stack :=
          stack [.d, .a, .b, .c, .k, .e, .factor, .pair, .upper, .lower] (eval (MachineState.readWord s.memory 80) k q) (nextKey k) rho} := by
   have gs := Table80RawRound53.gasSteps s (input q k) rho hstack hrun hactive hcode hfork hnp
   have hin : Table80Raw.inputStack (input q k) rho = stack [.d, .e, .c, .b, .k, .a, .factor, .pair, .upper, .lower] q k rho := rfl
   rw [hin, output_eq] at gs
   exact gs
 #print axioms gasSteps

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80CoreRound53
