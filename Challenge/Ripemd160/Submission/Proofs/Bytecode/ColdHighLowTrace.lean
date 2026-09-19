import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTraceCompose
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration ColdHighPaddingMemory StaggerPersistentFrame
noncomputable opaque gasSteps_lowRoute (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (i : Nat) (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i)
    (hlarge : 5225 ≤ input.size) :
    GasSteps
      {states input i with pc:=UInt256.ofNat 4714, stack:=frame (hashes input i) (DriverTrace.blockOffsetWord i) (LoopCompletionControl.limit input) maskRho}
      {lowState input i with pc:=UInt256.ofNat 4774, stack:=frame (hashes input i) (DriverTrace.blockOffsetWord i) (UInt256.ofNat input.size) maskRho} := by
  let s:=states input i
  let h:=hashes input i
  let off:=DriverTrace.blockOffsetWord i
  let lim:=LoopCompletionControl.limit input
  let r:=ColdOrdinaryPrepare.rest h off lim maskRho
  have hc : s.executionEnv.code=Artifact.submissionArtifact.code := states_code input i
  have hf : s.fork=.Osaka := states_fork input i
  have hr : s.halt=.Running := states_halt input i
  have hnp:=states_noPrecompile input i
  have hcal : s.executionEnv.calldata=input := states_calldata input i
  have ctx:=states_context input hfit hpositive i (by omega)
  have hsz : s.executionEnv.calldata.size<2^256 := by rw [hcal];exact calldata_lt_uint256 input hfit
  have hz : input.size%64=0 := by rw [hh,DriverTrace.blockOffset];omega
  have hlim : lim=UInt256.ofNat input.size := by simp only [lim,LoopCompletionControl.limit,LoopCompletionControl.limitNat,if_pos hz]
  have gp:=StaggerPersistentPadPrefix.gasSteps_prefix s (frame h off lim maskRho)
    (by simp [frame,maskRho]) hr hc hf hnp
  have ha : 35≤s.activeWords.toNat := ctx.active
  have gl:=ColdOrdinarySites.gasSteps_low s Paired144WordRound.factorPlusWord r (by rfl)
    (by simp [r,ColdOrdinaryPrepare.rest,maskRho]) hr ha hsz hc hf hnp
  rw [hcal] at gl
  have gl' : GasSteps {s with pc:=UInt256.ofNat 4715,stack:=frame h off lim maskRho}
      {lowState input i with pc:=UInt256.ofNat 4770, stack:=StaggerPad.highZero (UInt256.ofNat input.size)::frame h off lim maskRho} := gl
  have gf:=ColdOrdinarySites.gasSteps_branch_fall (lowState input i)
    (StaggerPad.highZero (UInt256.ofNat input.size)) (frame h off lim maskRho)
    (by simp [frame,maskRho]) hr (large_branch input hfit hlarge) hc hf hnp
  -- The old trampoline is gone: the JUMPI now falls through into the JUMPDEST,
  -- so `gf` already ends where `gr` used to.
  have gout := ColdTraceCompose.two gp (ColdTraceCompose.two gl' gf)
  exact gout.cast rfl (by rw [hlim])
#print axioms gasSteps_lowRoute

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
