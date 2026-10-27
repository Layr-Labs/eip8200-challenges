import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Return32Finish
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Return32Output
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ClosedEndianLiteralBounds
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedOutputMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashAfterModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Return32Serialize
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate

def value (h : Compression.HashState) : UInt256 :=
  DenseScheduleTemplate.packedWord (HoistedInherited.Return32Output.packedHash h)
/-- The finish path leaves the exit offset word below the result. -/
def result (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) : State :=
  HoistedInherited.Return32Finish.terminalResult (HoistedInherited.Return32Output.prepared s h) (UInt256.ofNat 9991)
    (HoistedInherited.Return32Finish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (HoistedInherited.Return32Output.packedHash h))
    (off :: limit :: rho)

theorem result_hReturn (s : State) (h : Compression.HashState) (off limit : UInt256)
    (rho : List UInt256) :
    (result s h off limit rho).hReturn = Data.Bytes.natToBytesPadded (value h).toNat 32 :=
  HoistedInherited.Return32Finish.hReturn_eq s h (UInt256.ofNat 9991) (off :: limit :: rho)

def gasSteps (s : State) (off limit : UInt256) (h : Compression.HashState)
    (rho : List UInt256) (hstack : rho.length ≤ 980) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = HoistedInherited.Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (h32 : s.executionEnv.calldata.size = 32) :
    GasSteps {s with pc := UInt256.ofNat 9949, stack := StaggerPersistentFrame.frame h off limit (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)}
      (result s h off limit (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)) := by
  have gp := HoistedInherited.Return32Output.gasSteps s off limit h
    (DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho) (by simp; omega) hrun hcode hfork hnp
  have gs := HoistedInherited.Return32Finish.gasSteps_stages (HoistedInherited.Return32Output.prepared s h)
    (HoistedInherited.Return32Output.packedHash h) off limit DenseScheduleTemplate.mask8
    DenseScheduleTemplate.mask16 rho (by omega) hcode hfork hrun hnp
  have gt := HoistedInherited.Return32Finish.gasSteps_terminal (HoistedInherited.Return32Output.prepared s h)
    (HoistedInherited.Return32Finish.finish DenseScheduleTemplate.mask8 DenseScheduleTemplate.mask16
      (HoistedInherited.Return32Output.packedHash h))
    (off :: limit :: DenseScheduleTemplate.mask8 :: DenseScheduleTemplate.mask16 :: rho)
    (by simp; omega) hcode hfork hrun hnp h32
  exact gp.trans (gs.trans gt)
#print axioms gasSteps
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Return32Serialize
