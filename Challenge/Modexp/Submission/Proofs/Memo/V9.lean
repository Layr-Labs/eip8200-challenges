import Challenge.Modexp.Submission.Proofs.Memo.V9.Trace
import Challenge.Modexp.Submission.Proofs.Memo.V9.Spec

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V9

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Logic Dispatch State Paths Trace

private def sound {s t : State} (path : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka))
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork h hrun hnp

private def soundOne {s t : State}
    {located : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka}
    (hrun : s.halt = .Running)
    (h : Challenge.EvmProof.Stepper.runLocated located s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocated_sound hcode hfork h hrun hnp

def gasSteps_match (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 2474) (returnedState input) :=
  ((((((sound preludePath rfl (run_prelude input) rfl rfl deployAddress_not_precompile).trans
    (sound chunk0Path rfl (run_chunk0 input) rfl rfl deployAddress_not_precompile)).trans
    (sound chunk1Path rfl (run_chunk1 input) rfl rfl deployAddress_not_precompile)).trans
    (sound branchPrefixPath rfl (run_branch_match_prefix input h) rfl rfl deployAddress_not_precompile)).trans
    (soundOne rfl (run_branch_jump input) rfl rfl deployAddress_not_precompile)).trans
    (sound returnPath rfl (run_return input) rfl rfl deployAddress_not_precompile))

def gasSteps_fallback (input : ByteArray) (h : guardDiff Data.checks input ≠ 0) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 2474) (Main.trampolineState input 1196) :=
  ((((((sound preludePath rfl (run_prelude input) rfl rfl deployAddress_not_precompile).trans
    (sound chunk0Path rfl (run_chunk0 input) rfl rfl deployAddress_not_precompile)).trans
    (sound chunk1Path rfl (run_chunk1 input) rfl rfl deployAddress_not_precompile)).trans
    (sound branchPath rfl (run_branch_mismatch input h) rfl rfl deployAddress_not_precompile)).trans
    (sound fallbackPrefixPath rfl (run_fallback_prefix input) rfl rfl deployAddress_not_precompile)).trans
    (soundOne rfl (run_fallback_jump input) rfl rfl deployAddress_not_precompile))

def gasSteps_pretest_taken (input : ByteArray) (hw : MachineState.readWord input 96 = UInt256.ofNat 73247641362558725300106169323372519318985509881989093824173738694050148637181) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 2432) (Main.trampolineState input 2656) :=
  (sound pretestPath rfl (run_pretest_prefix input) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_pretest_taken input hw) rfl rfl deployAddress_not_precompile)

def gasSteps_pretest_notTaken (input : ByteArray) (hw : MachineState.readWord input 96 ≠ UInt256.ofNat 73247641362558725300106169323372519318985509881989093824173738694050148637181) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 2432) (Main.trampolineState input 2474) :=
  (sound pretestPath rfl (run_pretest_prefix input) rfl rfl deployAddress_not_precompile).trans
    (sound pretestJumpPath rfl (run_pretest_notTaken input hw) rfl rfl deployAddress_not_precompile)

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (h : guardDiff Data.checks input = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  have hm : WordsMatch Data.checks input := (guardDiff_eq_zero_iff _ _).1 h
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned (MachineState.readPadded answerMemory 0 32) = _
  rw [answerMemory_read, Spec.spec_eq hm]

end Challenge.Modexp.Submission.Proofs.Memo.V9
