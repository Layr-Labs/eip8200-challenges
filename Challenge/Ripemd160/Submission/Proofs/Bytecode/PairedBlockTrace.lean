import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalBridge
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PairedBlockModel

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

theorem valid_return (s : State) (hcode : s.executionEnv.code = submissionBytecode) :
    Decode.isValidJumpDest s.executionEnv.code (UInt256.ofNat 483).toNat = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 296 = 483 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 296 (by rfl)
  rw [hpc] at h
  change Decode.isValidJumpDest s.executionEnv.code 483 = true
  rw [hcode]
  exact h

/-- Exact new compression call, including sparse scheduling and staggered rounds. -/
noncomputable def gasSteps_compress (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned (resultState s input i) input i) := by
  let q := scheduledState s i
  let ret := UInt256.ofNat 483
  let rho := driverRest input i
  have hactive : 34 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have gp := StaggerPrepare.gasSteps_prepare s input i h hfit hi ctx hcode hfork hrun hnp
  have gc := StaggerCore.gasSteps_core q (ret :: rho) (by simp [rho, driverRest])
    hrun hactive hcode hfork hnp
  let t : State := {q with memory := StaggerCoreModel.resultMemory q.memory}
  have gt := StaggerReturn.gasSteps t ret rho (by simp [rho, driverRest])
    hrun (valid_return t hcode) hcode hfork hnp
  have gall := gp.trans (gc.trans gt)
  apply gall.cast rfl
  have hm : StaggerCoreModel.resultMemory q.memory = (resultState s input i).memory :=
    StaggerFinalBridge.resultMemory_model s input i h hfit hi ctx
  change {q with pc := ret, stack := rho, memory := StaggerCoreModel.resultMemory q.memory} = _
  rw [hm]
  rfl
#print axioms gasSteps_compress
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
