import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFinish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PreSerialize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerTailBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ClosedEndianLiteralBounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def value (h : Compression.HashState) : UInt256 :=
  DenseScheduleTemplate.packedWord (StaggerPersistentOutput.packedHash h)
/-- The epilogue's final state, entered at 4733 with the block-exit stack of the last block. -/
def result (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) : State :=
  PreSerialize.resultQ s h (PersistentStaggerTailBridge.exitQ memory h off cont) rho

theorem result_hReturn (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) :
    (result s memory h off cont rho).hReturn =
      Data.Bytes.natToBytesPadded (value (PersistentStaggerFunctional.result memory h)).toNat 32 := by
  rw [result, PreSerialize.resultQ_hReturn, PersistentStaggerTailBridge.exitQ,
    PersistentStaggerTailBridge.result_eq]
  rfl

def gasSteps (s : State) (memory : ByteArray) (h : Compression.HashState) (off cont : UInt256)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 4733, stack := PersistentStaggerTailBridge.preStack memory h off cont (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)}
      (result s memory h off cont rho) :=
  PreSerialize.gasStepsQ s h (PersistentStaggerTailBridge.exitQ memory h off cont) rho hstack hrun hcode hfork hnp
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerialize
