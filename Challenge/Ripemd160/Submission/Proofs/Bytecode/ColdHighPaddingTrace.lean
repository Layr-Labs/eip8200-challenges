import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTraceCompose
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighModel
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration ColdHighPaddingMemory StaggerPersistentFrame
noncomputable opaque gasSteps_padding (input : ByteArray) (hfit : CalldataFits input) (hn32 : input.size≠32) (i : Nat) :
    GasSteps {lowState input i with pc:=UInt256.ofNat 4760,stack:=frame (hashes input i) (DriverTrace.blockOffsetWord i) (UInt256.ofNat input.size) maskRho}
      {paddedState input i with pc:=UInt256.ofNat 509,stack:=frame (hashes input i) (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) maskRho} := by
  let h:=hashes input i
  let off:=DriverTrace.blockOffsetWord i
  have hc : (lowState input i).executionEnv.code=Artifact.submissionArtifact.code := states_code input i
  have hf : (lowState input i).fork=.Osaka := states_fork input i
  have hr : (lowState input i).halt=.Running := states_halt input i
  have hnp:=states_noPrecompile input i
  have hcal : (lowState input i).executionEnv.calldata=input := states_calldata input i
  have gp := StaggerPersistentStart.gasSteps_partial (lowState input i) h off
    (UInt256.ofNat input.size) maskRho (by decide) hr hc hf hnp
    (by rw [hcal]; exact Nat.lt_trans hfit (by norm_num)) (by simpa [hcal] using hn32)
  rw [PadLimitArithmetic.rounded_input] at gp
  have gpad:=PaddingTraceGeneral.gasSteps_padBody input (lowState input i)
    (frame h off (Padding.paddedWord input) maskRho) (by simp [frame,maskRho]) (by rfl)
    hcal hr hc hf hnp hfit hn32
  have gpad' : GasSteps
      {lowState input i with pc:=UInt256.ofNat 4760,stack:=frame h off (UInt256.ofNat input.size) maskRho}
      {paddedState input i with pc:=UInt256.ofNat 508,stack:=frame h off (Padding.paddedWord input) maskRho} := gp.trans gpad
  have gj:=StaggerPersistentLoopSites.gasSteps_join (paddedState input i)
    (frame h off (Padding.paddedWord input) maskRho) (by simp [frame,maskRho]) hr hc hf hnp
  exact ColdTraceCompose.two gpad' gj
#print axioms gasSteps_padding

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
