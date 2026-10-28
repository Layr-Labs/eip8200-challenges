import Challenge.Ripemd160.Submission.Local20261028.ColdArtifact
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentFinish
import Challenge.Ripemd160.Submission.Local20261028.ColdStaggerPersistentOutput
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StaggerPersistentSerialize
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def value (h : Compression.HashState) : UInt256 :=
  DenseScheduleTemplate.packedWord (Control.StaggerPersistentOutput.packedHash h)
/-- The finish path leaves the exit offset word below the result. -/
def result (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  Control.StaggerPersistentFinish.terminalResult (Control.StaggerPersistentOutput.prepared s h) (UInt256.ofNat 8439)
    (Control.StaggerPersistentFinish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (Control.StaggerPersistentOutput.packedHash h))
    (off :: limit :: rho)

theorem result_hReturn (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) :
    (result s h off limit rho).hReturn = Data.Bytes.natToBytesPadded (value h).toNat 32 :=
  Control.StaggerPersistentFinish.hReturn_eq s h (UInt256.ofNat 8439) (off :: limit :: rho)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Control.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps {s with pc := UInt256.ofNat 8397, stack := StaggerPersistentFrame.frame h off limit (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)}
      (result s h off limit (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)) := by
  have gp := Control.StaggerPersistentOutput.gasSteps s off limit h
    (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho) (by simp; omega) hrun hcode hfork hnp
  have gs := Control.StaggerPersistentFinish.gasSteps_stages (Control.StaggerPersistentOutput.prepared s h)
    (Control.StaggerPersistentOutput.packedHash h) off limit DenseScheduleTemplate.mask8
    DenseScheduleTemplate.mask16 rho (by omega) hcode hfork hrun hnp
  have gt := Control.StaggerPersistentFinish.gasSteps_terminal (Control.StaggerPersistentOutput.prepared s h)
    (Control.StaggerPersistentFinish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (Control.StaggerPersistentOutput.packedHash h))
    (off :: limit :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)
    (by simp; omega) hcode hfork hrun hnp
  exact gp.trans (gs.trans gt)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.StaggerPersistentSerialize
