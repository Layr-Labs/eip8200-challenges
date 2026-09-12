import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80BootstrapBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Prepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80FinalBridgeWide
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Bootstrap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Core
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80TailSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PairedBlockModel

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

/-- Complete exact compression call for every block admitted by the outer invariant. -/
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
  let ret := DriverTrace.blockOffsetWord i
  let rho : List UInt256 := [Padding.paddedWord input]
  let initial := Table80BootstrapBridge.initialLane h
  let final := Table80Core.physicalFinalLane q.memory initial
  have hactive : 34 ≤ q.activeWords.toNat := scheduled_active s input i hfit hi
  have hh : StackMemory.hashAt q.memory = Compression.embedHash h :=
    (Table80FinalBridge.scheduled_hashAt s i).trans ctx.hash
  have gp := Table80Prepare.gasSteps_prepare s input i h hfit hi ctx hcode hfork hrun hnp
  have gb := Table80BootstrapBridge.gasSteps_clean q h (ret :: rho) hh
    (by simp [rho]) hrun hactive hcode hfork hnp
  have gc := Table80Core.gasSteps_core q initial ret rho (by simp [rho])
    hrun hactive hcode hfork hnp
  have gt := Table80TailSite.gasSteps q ret final Table80WideCoreBridge.wideFactorWord rho (by simp [rho])
    hrun hactive hcode hfork hnp
  have gall := gp.trans (gb.trans (gc.trans gt))
  apply gall.cast rfl
  have hm : Table80ConsumedTerminalTail.resultMemory q.memory final = (resultState s input i).memory :=
    Table80FinalBridge.physical_resultMemory_model s input i h hfit hi ctx
  change {q with pc := UInt256.ofNat 4707, stack := ret :: rho, memory := Table80ConsumedTerminalTail.resultMemory q.memory final} = _
  rw [hm]
  rfl

#print axioms gasSteps_compress
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
