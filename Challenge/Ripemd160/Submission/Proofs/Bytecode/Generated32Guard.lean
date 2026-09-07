import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Logic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Spec

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! Symbolic execution of the exact-word EOF guard. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Guard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open Generated32Data

abbrev Located := DirectGuard.Located
abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

def sizePath : List Located :=
  [DirectGuard.opAt 3234 .JUMPDEST, DirectGuard.opAt 3235 .CALLDATASIZE,
   DirectGuard.pushAt 3236 1 32, DirectGuard.opAt 3237 .XOR,
   DirectGuard.pushAt 3238 2 0x12ce, DirectGuard.opAt 3239 .JUMPI]

def wordPath : List Located :=
  [DirectGuard.pushAt 3240 0 0, DirectGuard.opAt 3241 .CALLDATALOAD,
   DirectGuard.pushAt 3242 32 targetWord, DirectGuard.opAt 3243 .XOR,
   DirectGuard.pushAt 3244 2 0x12ce, DirectGuard.opAt 3245 .JUMPI]

def copySetupPath : List Located :=
  [DirectGuard.pushAt 3246 1 20, DirectGuard.pushAt 3247 2 0x1347,
   DirectGuard.pushAt 3248 1 12]

def returnPath : List Located :=
  [DirectGuard.pushAt 3250 1 32, DirectGuard.pushAt 3251 0 0,
   DirectGuard.opAt 3252 .RETURN]

def sizeMatched (input : ByteArray) : State := Execution.atPC input 0x14c2

def preCopyState : State :=
  { initialState submissionBytecode targetInput 0 with
    pc := UInt256.ofNat 0x14f1
    stack := [UInt256.ofNat 12, UInt256.ofNat 0x1347, UInt256.ofNat 20] }

def answerMemory : ByteArray :=
  MachineState.writeBytes ByteArray.empty
    (MachineState.readPadded submissionBytecode 0x1347 20) 12

def copiedState : State :=
  { initialState submissionBytecode targetInput 0 with
    pc := UInt256.ofNat 0x14f2
    activeWords := (initialState submissionBytecode targetInput 0).activeWordsAfterUInt256 12 20
    memory := answerMemory }

def returnedState : State :=
  { copiedState with
    pc := UInt256.ofNat 0x14f6
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

private def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

private theorem fallbackDestination :
    Decode.isValidJumpDest submissionBytecode 0x12ce = true := by
  have hget : Artifact.submissionArtifact.instructions[3025]? =
      some (.op .JUMPDEST) := by rfl
  have hpc : Artifact.submissionArtifact.instructionPC 3025 = 0x12ce := by rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3025 hget
  rwa [hpc] at h

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 32) :
    run sizePath (Execution.atPC input 0x14b9) =
      some (Execution.atPC input 0x12ce) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have hword : UInt256.ofNat input.size ≠ UInt256.ofNat 32 := by
    intro heq
    have hnat := congrArg UInt256.toNat heq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by norm_num)] at hnat
    exact hsize hnat
  have htrue : UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 32) (UInt256.ofNat input.size)) :=
    Generated32Logic.xor_isTrue_of_ne _ _ hword.symm
  simp [sizePath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    Execution.atPC, htrue, fallbackDestination, UInt256.isTrue,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_size_match (input : ByteArray) (hsize : input.size = 32) :
    run sizePath (Execution.atPC input 0x14b9) = some (sizeMatched input) := by
  have hzero : UInt256.xor (UInt256.ofNat 32)
      (UInt256.ofNat input.size) = 0 := by
    rw [hsize]
    exact (KnownInputLogic.wordXor_eq_zero_iff
      (UInt256.ofNat 32) (UInt256.ofNat 32)).2 rfl
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor (UInt256.ofNat 32) (UInt256.ofNat input.size)) := by
    rw [hzero]
    decide
  simp [sizePath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    Execution.atPC, sizeMatched, hsize, hzero, hfalse, UInt256.isTrue,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_word_fail (input : ByteArray) (hsize : input.size = 32)
    (hne : input ≠ targetInput) :
    run wordPath (sizeMatched input) = some (Execution.atPC input 0x12ce) := by
  have hword : MachineState.readWord input 0 ≠ targetWord := by
    exact fun heq => hne ((Generated32Logic.readWord_eq_target_iff input hsize).1 heq)
  have htrue : UInt256.isTrue
      (UInt256.xor targetWord (MachineState.readWord input 0)) :=
    Generated32Logic.xor_isTrue_of_ne _ _ hword.symm
  simp [wordPath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    Execution.atPC, sizeMatched, htrue, fallbackDestination, UInt256.isTrue,
    BooleanSelect.xor_comm,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_target_setup :
    run (sizePath ++ wordPath ++ copySetupPath)
      (Execution.atPC targetInput 0x14b9) = some preCopyState := by
  simp [sizePath, wordPath, copySetupPath, DirectGuard.opAt, DirectGuard.pushAt,
    DirectGuard.wfOp, Execution.atPC, sizeMatched, preCopyState,
    targetInput_size, targetInput_readWord,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, KnownInputLogic.wordXor_eq_zero_iff]

def gasSteps_codecopy : GasSteps preCopyState copiedState := by
  let pre := preCopyState
  let cost := Gas.codecopyTotal pre (UInt256.ofNat 12) (UInt256.ofNat 20)
  refine GasSteps.one cost ?_
  intro gas hgas
  have hdec : (withGas pre gas).decodedOp = some .CODECOPY := by
    have hcode : (withGas pre gas).executionEnv.code =
        Artifact.submissionArtifact.code := by rfl
    have hpc : (withGas pre gas).pc.toNat =
        Artifact.submissionArtifact.instructionPC 3249 := by rfl
    exact Challenge.EvmProof.Stepper.decodes_of_artifact
      Artifact.submissionArtifact (withGas pre gas) 3249 (.op .CODECOPY)
      hcode hpc (by rfl) (by exact ⟨by decide, trivial, rfl⟩)
  apply EVM.Step.running
  · rfl
  · exact deployAddress_not_precompile
  · have hstack : (withGas pre gas).stack =
        [UInt256.ofNat 12, UInt256.ofNat 0x1347, UInt256.ofNat 20] := by rfl
    have hcap : (withGas pre gas).stack.length +
        Operation.pushArity .CODECOPY ≤ 1024 + Operation.popArity .CODECOPY := by
      norm_num [pre, preCopyState, withGas, Operation.pushArity,
        Operation.popArity]
    have hstep := StepRunning.codecopy (withGas pre gas)
      (UInt256.ofNat 12) (UInt256.ofNat 0x1347) (UInt256.ofNat 20) []
      hdec hstack hgas hcap
    simpa [pre, cost, preCopyState, copiedState, answerMemory, withGas,
      Gas.codecopyTotal, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.succ_ofNat (n := 5361) (by norm_num)] using hstep

theorem run_return : run returnPath copiedState = some returnedState := by
  simp [returnPath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    copiedState, returnedState,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

def gasSteps_target :
    GasSteps (Execution.atPC targetInput 0x14b9) returnedState :=
  (sound (sizePath ++ wordPath ++ copySetupPath) run_target_setup).trans
    (gasSteps_codecopy.trans (sound returnPath run_return))

def gasSteps_fallback (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ targetInput) :
    GasSteps (Execution.atPC input 0x14b9) (Execution.atPC input 0x12ce) := by
  by_cases hsize : input.size = 32
  · exact (sound sizePath (run_size_match input hsize)).trans
      (sound wordPath (run_word_fail input hsize hne))
  · exact sound sizePath (run_size_fail input hfit hsize)

theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = paddedDigest := by
  unfold answerMemory
  rw [submissionBytecode_readDigest]
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Generated32Guard
