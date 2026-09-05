import Challenge.Modexp.Submission.Proofs.Memo.Dispatch

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Memo.V0

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Memo
open Dispatch

def prefixPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1035 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 1036 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.pushAt 1037 2 1196
  ]

def notTakenPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.opAt 1035 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPDEST)),
   Main.opAt 1036 (EvmSemantics.Operation.Env (EvmSemantics.Operation.EnvOps.CALLDATASIZE)),
   Main.pushAt 1037 2 1196,
   Main.opAt 1038 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))
  ]

def returnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [
   Main.pushAt 1039 0 0,
   Main.pushAt 1040 0 0,
   Main.opAt 1041 (EvmSemantics.Operation.System (EvmSemantics.Operation.SystemOps.RETURN))
  ]

def jumpState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1413
      stack := [UInt256.ofNat 1196, UInt256.ofNat input.size] }

def jumpLocated : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  Main.opAt 1038 (EvmSemantics.Operation.StackMemFlow (EvmSemantics.Operation.StackMemFlowOps.JUMPI))

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
      pc := UInt256.ofNat 1416
      stack := []
      activeWords := UInt256.ofNat 0
      halt := .Returned
      hReturn := MachineState.readPadded ByteArray.empty 0 0 }

theorem run_prefix (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock prefixPath (Main.trampolineState input 1408) =
      some (jumpState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [prefixPath, jumpState, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_jump_taken (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : input.size ≠ 0) :
    Challenge.EvmProof.Stepper.runLocated jumpLocated (jumpState input) =
      some (Main.trampolineState input 1196) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  have hpc : (jumpState input).pc.toNat = Artifact.submissionArtifact.instructionPC 1038 := by
    simp [jumpState, initialState, PCs.pc1, Challenge.EvmProof.Word.word_toNat_ofNat]
  exact (Step.runLocated_jumpi_taken jumpLocated rfl (jumpState input) 1196 (UInt256.ofNat input.size) [] hpc rfl (by simp)
    (Logic.isTrue_ofNat hsize h) rfl (by norm_num) hjump).trans rfl

theorem run_notTaken (input : ByteArray) (h : input.size = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock notTakenPath (Main.trampolineState input 1408) =
      some (Main.trampolineState input 1414) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [notTakenPath, h, Logic.not_isTrue_zero, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (Main.trampolineState input 1414) =
      some (returnedState input) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [returnPath, returnedState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Main.trampolineState, PCs.pc1,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

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

def gasSteps_match (input : ByteArray) (h : input.size = 0) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1408) (returnedState input) :=
  (sound notTakenPath rfl (run_notTaken input h) rfl rfl deployAddress_not_precompile).trans
    (sound returnPath rfl (run_return input) rfl rfl deployAddress_not_precompile)

def gasSteps_fallback (input : ByteArray) (hsize : input.size < 2 ^ 256) (h : input.size ≠ 0) :
    Challenge.EvmProof.GasSteps (Main.trampolineState input 1408) (Main.trampolineState input 1196) :=
  (sound prefixPath rfl (run_prefix input) rfl rfl deployAddress_not_precompile).trans
    (soundOne rfl (run_jump_taken input hsize h) rfl rfl deployAddress_not_precompile)

@[simp] theorem returnedState_isDone (input : ByteArray) :
    (returnedState input).isDone = true := by
  simp [returnedState, State.isDone, State.isHalted, State.isRunning]
  rfl

theorem returnedState_result (input : ByteArray) (h : input.size = 0) :
    (returnedState input).toResult = .returned (spec input) := by
  rw [State.toResult_returned _ (by rfl)]
  change ExecutionResult.returned (MachineState.readPadded ByteArray.empty 0 0) = _
  rw [Logic.eq_empty_of_size_eq_zero input h]
  rw [show MachineState.readPadded ByteArray.empty 0 0 = ByteArray.empty by decide +kernel,
    show spec ByteArray.empty = ByteArray.empty by decide +kernel]

end Challenge.Modexp.Submission.Proofs.Memo.V0
