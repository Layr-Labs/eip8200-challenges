import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80PrepareModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80PadJump
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Prepare
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PairedBlockModel
opaque gasSteps_prepare_hit (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hhit : input.size = DriverTrace.blockOffset i) :
    GasSteps (DriverTrace.compressEntry s input i)
      {scheduledState s i with pc := UInt256.ofNat 1066, stack := Table80Raw.cache ++ (UInt256.ofNat 512 :: driverRest input i)} := by
  let q := scheduledState s i
  let rho := UInt256.ofNat 512 :: driverRest input i
  have hfit256 : s.executionEnv.calldata.size < 2^256 := by
    rw [ctx.calldata]
    exact calldata_lt_uint256 input hfit
  have heq : s.executionEnv.calldata.size = (DriverTrace.blockOffsetWord i).toNat := by
    rw [ctx.calldata, blockOffsetWord_toNat input hfit i hi]
    exact hhit
  have ghit := Table80Dispatch.gasSteps_hit s (DriverTrace.messageOffsetWord i)
    (UInt256.ofNat 512) (DriverTrace.blockOffsetWord i) [Padding.paddedWord input]
    (by simp) hrun hfit256 heq hcode hfork hnp
  have gtouch := Table80Dispatch.gasSteps_prefix s (UInt256.ofNat 512) (messagePointer i)
    (driverRest input i) (by simp [driverRest]) hrun
    hcode hfork hnp
  let a : State := {s with activeWords := DenseScheduleTemplate.loadedActiveWords s (UInt256.ofNat (messagePointer i))}
  have ha : a = s := by
    dsimp only [a]
    rw [scheduled_active_eq s input i h hfit hi ctx]
  have ga : GasSteps (DriverTrace.compressEntry s input i)
      {a with pc := UInt256.ofNat 410, stack := rho} := by
    rw [ha]
    exact ghit.trans gtouch
  have gbody := Table80SetupSites.gasSteps_pad a (UInt256.ofNat 512) (driverRest input i)
    (by simp [driverRest]) hrun (scheduled_active s input i hfit hi) hfit256 hcode hfork hnp
  have hmem : PairTablePad.resultMemory a.memory
      (UInt256.ofNat a.executionEnv.calldata.size) = q.memory :=
    scheduled_memory_calldata s input i h hfit hi ctx hhit
  have gb : GasSteps {a with pc := UInt256.ofNat 410, stack := rho}
      {q with pc := UInt256.ofNat 508, stack := Table80Raw.cache ++ rho} := by
    apply gbody.cast rfl
    rw [hmem]
    rfl
  have gjump := Table80PadJump.gasSteps_jump q (Table80Raw.cache ++ rho)
    (by simp [rho, driverRest, Table80Raw.cache]) hrun hcode hfork hnp
  exact ga.trans (gb.trans gjump)

opaque gasSteps_prepare_miss (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hmiss : input.size ≠ DriverTrace.blockOffset i) :
    GasSteps (DriverTrace.compressEntry s input i)
      {scheduledState s i with pc := UInt256.ofNat 1066, stack := Table80Raw.cache ++ (UInt256.ofNat 512 :: driverRest input i)} := by
  have hfit256 : s.executionEnv.calldata.size < 2^256 := by
    rw [ctx.calldata]
    exact calldata_lt_uint256 input hfit
  have hne : s.executionEnv.calldata.size ≠ (DriverTrace.blockOffsetWord i).toNat := by
    rw [ctx.calldata, blockOffsetWord_toNat input hfit i hi]
    exact hmiss
  have gmiss := Table80Dispatch.gasSteps_miss s (DriverTrace.messageOffsetWord i)
    (UInt256.ofNat 512) (DriverTrace.blockOffsetWord i) [Padding.paddedWord input]
    (by simp) hrun hfit256 hne hcode hfork hnp
  have gnormal := Table80SetupSites.gasSteps_normal s (UInt256.ofNat 512)
    (messagePointer i) (driverRest input i) (by simp [driverRest]) hrun
    (messagePointer_lower i) (messagePointer_bound input hfit i hi) hcode hfork hnp
  exact gmiss.trans gnormal

opaque gasSteps_prepare (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      {scheduledState s i with pc := UInt256.ofNat 1066, stack := Table80Raw.cache ++ (UInt256.ofNat 512 :: driverRest input i)} := by
  by_cases hhit : input.size = DriverTrace.blockOffset i
  · exact gasSteps_prepare_hit s input i h hfit hi ctx hcode hfork hrun hnp hhit
  · exact gasSteps_prepare_miss s input i h hfit hi ctx hcode hfork hrun hnp hhit

#print axioms gasSteps_prepare_hit
#print axioms gasSteps_prepare_miss
#print axioms gasSteps_prepare
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Table80Prepare
