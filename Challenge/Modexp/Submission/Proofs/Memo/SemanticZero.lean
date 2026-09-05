import Challenge.Modexp.Submission.Proofs.Memo.V3.Trace
import Challenge.EvmProof.Bytes

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

/-!
Modified September 5, 2026. Apache-2.0. Complete source attempt; not a build log.
The general M=0 case needs no exact-vector identity. Reuse the existing, unchanged
empty-return machine trace and prove its result directly from the specification.
-/
namespace Challenge.Modexp.Submission.Proofs.Memo.SemanticZero
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo

theorem modulusSize_zero (input : ByteArray)
    (hw : MachineState.readWord input 64 = UInt256.ofNat 0) :
    modulusSize input = 0 := by
  have hn := congrArg UInt256.toNat hw
  change (MachineState.readWord input 64).toNat = 0 at hn
  exact (Challenge.EvmProof.Bytes.readWord_toNat input 64).symm.trans hn

def gasSteps_return (input : ByteArray) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1698)
      (V3.State.returnedState input) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka V3.Paths.returnPath rfl rfl
    (V3.Trace.run_return input) rfl deployAddress_not_precompile

theorem returnedState_result (input : ByteArray)
    (hw : MachineState.readWord input 64 = UInt256.ofNat 0) :
    (V3.State.returnedState input).toResult = .returned (spec input) := by
  have hm := modulusSize_zero input hw
  have hs : spec input = ByteArray.empty := by simp [spec, hm]
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned (MachineState.readPadded ByteArray.empty 0 0) = _
  rw [show MachineState.readPadded ByteArray.empty 0 0 = ByteArray.empty by decide +kernel, hs]

end Challenge.Modexp.Submission.Proofs.Memo.SemanticZero
