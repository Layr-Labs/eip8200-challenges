import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackPC

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardBranch
open EvmSemantics EvmSemantics.EVM
open Challenge.Ripemd160 Challenge.EvmProof
open ExactGuardLogic ExactGuardState ExactGuardPaths

private theorem returnDest_valid :
    Decode.isValidJumpDest submissionBytecode 5410 = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 2965 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 2965 = 5410 := by
    rw [StackPC.instructionPC_eq_byteLength]
    decide
  rw [hp] at h
  exact h

private theorem fallbackDest_valid :
    Decode.isValidJumpDest submissionBytecode 0x3ee = true := by
  have h := Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  have hp : Artifact.submissionArtifact.instructionPC 682 = 0x3ee := by
    rw [StackPC.instructionPC_eq_byteLength]
    decide
  rw [hp] at h
  exact h

def branchPath := branchIsZeroPath ++ branchPushPath ++ branchJumpPath

theorem run_branch_match (input : ByteArray)
    (h : guardDiff input = 0) :
    Stepper.runLocatedBlock branchPath (diffState input 5401 (guardDiff input)) =
      some (branchState input 5410) := by
  have hz := diff_isZero_one input h
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  simp (config := { maxSteps := 1000000 }) [branchPath, branchIsZeroPath,
    branchPushPath, branchJumpPath, diffState, branchState, atPC, hz, htrue,
    returnDest_valid, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_branch_fallback (input : ByteArray)
    (h : guardDiff input ≠ 0) :
    Stepper.runLocatedBlock branchPath (diffState input 5401 (guardDiff input)) =
      some (branchState input 5406) := by
  have hz := diff_isZero_zero input h
  have htrue : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 1000000 }) [branchPath, branchIsZeroPath,
    branchPushPath, branchJumpPath, diffState, branchState, atPC, hz, htrue,
    returnDest_valid, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_fallback (input : ByteArray) :
    Stepper.runLocatedBlock fallbackPath (branchState input 5406) =
      some (fallbackState input) := by
  simp (config := { maxSteps := 1000000 }) [fallbackPath, fallbackState,
    branchState, atPC, fallbackDest_valid, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_return (input : ByteArray) :
    Stepper.runLocatedBlock returnPath (branchState input 5410) =
      some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [returnPath, returnedState,
    branchState, atPC, answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

private def sound {s t : State}
    (path : List (Stepper.Located Artifact.submissionArtifact .Osaka))
    (h : Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka path
    hcode hfork h hrun hnp

def gasSteps_match (input : ByteArray) (h : guardDiff input = 0) :
    GasSteps (entryState input) (returnedState input) :=
  (ExactGuardTrace.gasSteps_scan input).trans
    ((sound branchPath (run_branch_match input h) rfl rfl rfl deployAddress_not_precompile).trans
      (sound returnPath (run_return input) rfl rfl rfl deployAddress_not_precompile))

def gasSteps_fallback (input : ByteArray) (h : guardDiff input ≠ 0) :
    GasSteps (entryState input) (fallbackState input) :=
  (ExactGuardTrace.gasSteps_scan input).trans
    ((sound branchPath (run_branch_fallback input h) rfl rfl rfl deployAddress_not_precompile).trans
      (sound fallbackPath (run_fallback input) rfl rfl rfl deployAddress_not_precompile))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardBranch
