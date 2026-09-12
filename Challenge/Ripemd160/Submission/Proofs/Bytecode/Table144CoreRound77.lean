import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144RawRound77
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CoreCommon
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CoreRound77
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof PairedLaneUInt256Bridge Paired144WordRound
open Table144CoreCommon
def input (q : WordLane) (k : UInt256) : Table144Raw.Input :=
  ⟨word .d q k, word .k q k, word .c q k, word .b q k, word .e q k, word .a q k, word .factor q k, word .pair q k, word .upper q k, word .lower q k⟩
def eval (message k : UInt256) (q : WordLane) : WordLane := wordStep 4 8 13 message k q
def nextKey (k : UInt256) : UInt256 := k
theorem output_eq (memory : ByteArray) (q : WordLane) (k : UInt256) (rho : List UInt256) :
    Table144RawRound77.outputStack memory (input q k) rho =
      stack [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (eval (MachineState.readWord memory 54) k q) (nextKey k) rho := by
  simp only [Table144RawRound77.outputStack, input, stack, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Table144CoreCommon.word, eval, nextKey,
    wordStep, wordT, wordSum, rawWordStep2, hoistedSum, hoistedBoolean, rawFinish,
    boolean_zero, boolean_one, boolean_three, boolean_four,
    PairedLaneBooleanFactoring.factoredWord, PairedLaneBooleanSynthesis.oneWord,
    PairedLaneBooleanSynthesis.threeWord, List.cons.injEq, and_true]
  simp only [wordRotate, usesCompact, wordScale, wordShift, wordCompact]
  simp
  all_goals simp only [Table144CoreCommon.add_comm, Table144CoreCommon.add_left_comm,
    Table144CoreCommon.add_assoc, Table144CoreCommon.mul_comm, Table144CoreCommon.mul_one,
    Table144CoreCommon.land_comm, Table144CoreCommon.lor_comm,
    Table144CoreCommon.xor_comm, Table144CoreCommon.xor_left_comm, Table144CoreCommon.xor_assoc]
  all_goals trivial
#print axioms output_eq

 theorem nextKey_physical : nextKey (Paired144Algorithm.physicalKey 77) =
     Paired144Algorithm.physicalKey 78 := by decide

 theorem eval_physical (message : UInt256) (q : WordLane) :
     eval message (Paired144Algorithm.physicalKey 77) q = Paired144Algorithm.step 77 message q := by rfl

 def gasSteps (s : State) (q : WordLane) (k : UInt256) (rho : List UInt256)
     (hstack : rho.length ≤ 996) (hrun : s.halt = .Running)
     (hactive : 53 ≤ s.activeWords.toNat)
     (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
     (hfork : s.fork = .Osaka)
     (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
       s.executionEnv.fork s.executionEnv.codeAddr = false) :
     Challenge.EvmProof.GasSteps {s with pc := UInt256.ofNat 4492, stack := stack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] q k rho}
       {s with pc := UInt256.ofNat 4536, stack :=
          stack [.d, .k, .b, .c, .a, .e, .factor, .pair, .upper, .lower] (eval (MachineState.readWord s.memory 54) k q) (nextKey k) rho} := by
   have gs := Table144RawRound77.gasSteps s (input q k) rho hstack hrun hactive hcode hfork hnp
   have hin : Table144Raw.inputStack (input q k) rho = stack [.d, .k, .c, .b, .e, .a, .factor, .pair, .upper, .lower] q k rho := rfl
   rw [hin, output_eq] at gs
   exact gs
 #print axioms gasSteps

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table144CoreRound77
