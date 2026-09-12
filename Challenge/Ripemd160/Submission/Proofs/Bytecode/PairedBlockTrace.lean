import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerFinalBridge
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PairedBlockModel

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

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
  let rho := driverRest input i
  have hactive : 34 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have gp := StaggerPrepare.gasSteps_prepare s input i h hfit hi ctx hcode hfork hrun hnp
  have gc := StaggerCore.gasSteps_core q rho (by simp [rho, driverRest])
    hrun hactive hcode hfork hnp
  have gall := gp.trans gc
  apply gall.cast rfl
  have hm : StaggerCoreModel.resultMemory q.memory = (resultState s input i).memory :=
    StaggerFinalBridge.resultMemory_model s input i h hfit hi ctx
  change {q with pc := UInt256.ofNat 4675, stack := rho, memory := StaggerCoreModel.resultMemory q.memory} = _
  rw [hm]
  rfl
#print axioms gasSteps_compress
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
