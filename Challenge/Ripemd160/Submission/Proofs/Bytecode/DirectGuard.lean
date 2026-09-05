import Challenge.Ripemd160.Submission.Proofs.Bytecode.ExactGuardSpec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputCompactLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp (by decide) trivial rfl⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl) : Located :=
  ⟨index, .push width value, hget, by decide⟩

def sizePath : List Located :=
  [opAt 2813 .JUMPDEST, opAt 2814 .CALLDATASIZE, pushAt 2815 2 1000,
   opAt 2816 .EQ, pushAt 2817 2 4828, opAt 2818 .JUMPI]

def sizeFallbackPath : List Located :=
  [pushAt 2819 2 1006, opAt 2820 .JUMP]

def checkEntryPath : List Located :=
  [opAt 2821 .JUMPDEST, pushAt 2822 0 0, opAt 2823 .CALLDATALOAD,
   opAt 2824 (.Dup ⟨0, by decide⟩), pushAt 2825 8 7016996765293437281,
   opAt 2826 (.Dup ⟨0, by decide⟩), pushAt 2827 1 64, opAt 2828 .SHL,
   opAt 2829 .OR, opAt 2830 (.Dup ⟨0, by decide⟩), pushAt 2831 1 128,
   opAt 2832 .SHL, opAt 2833 .OR, opAt 2834 .XOR, pushAt 2835 1 32]

def loopPath : List Located :=
  [opAt 2836 .JUMPDEST, opAt 2837 (.Dup ⟨0, by decide⟩),
   opAt 2838 .CALLDATALOAD, opAt 2839 (.Dup ⟨3, by decide⟩),
   opAt 2840 .XOR, opAt 2841 (.Swap ⟨0, by decide⟩),
   opAt 2842 (.Swap ⟨1, by decide⟩), opAt 2843 .OR,
   opAt 2844 (.Swap ⟨0, by decide⟩), pushAt 2845 1 32, opAt 2846 .ADD,
   pushAt 2847 2 992, opAt 2848 (.Dup ⟨1, by decide⟩), opAt 2849 .LT,
   pushAt 2850 2 4854, opAt 2851 .JUMPI]

def tailPath : List Located :=
  [opAt 2852 .POP, pushAt 2853 2 992, opAt 2854 .CALLDATALOAD,
   pushAt 2855 1 192, opAt 2856 .SHR, opAt 2857 (.Dup ⟨2, by decide⟩),
   pushAt 2858 1 192, opAt 2859 .SHR, opAt 2860 .XOR, opAt 2861 .OR,
   opAt 2862 (.Swap ⟨0, by decide⟩), opAt 2863 .POP,
   pushAt 2864 2 1006, opAt 2865 .JUMPI]

def returnPath : List Located :=
  [pushAt 2866 20 972889429405991776604892044862621566948497025487,
   pushAt 2867 0 0, opAt 2868 .MSTORE, pushAt 2869 1 32,
   pushAt 2870 0 0, opAt 2871 .RETURN]

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

def sizeMatched (input : ByteArray) : State := atPC input 0x12dc
def sizeFailed (input : ByteArray) : State := atPC input 0x12d8
def fallbackState (input : ByteArray) : State := atPC input 0x3ee

def loopState (input : ByteArray) (n : Nat) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x12f6
    stack := [UInt256.ofNat (32 * (n + 1)), loopAcc input n, referenceWord input] }

def loopExitState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x130b
    stack := [UInt256.ofNat 992, loopAcc input 30, referenceWord input] }

def returnEntry (input : ByteArray) : State := atPC input 0x131f

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray :=
  storeWord ByteArray.empty 0 ExactGuardSpec.paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 0x1339
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

private abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

private theorem expandedFullWord :
    UInt256.lor
      (UInt256.shiftLeft
        (UInt256.lor
          (UInt256.shiftLeft (UInt256.ofNat 7016996765293437281) (UInt256.ofNat 64))
          (UInt256.ofNat 7016996765293437281))
        (UInt256.ofNat 128))
      (UInt256.lor
        (UInt256.shiftLeft (UInt256.ofNat 7016996765293437281) (UInt256.ofNat 64))
        (UInt256.ofNat 7016996765293437281)) = KnownInputData.fullWord := by decide

theorem run_size_target :
    run sizePath (Execution.atPC KnownInputData.targetInput 0x12ce) =
      some (sizeMatched KnownInputData.targetInput) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12dc = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2821 (by rfl)
  simp [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    KnownInputData.targetInput_size, hdest, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) :
    run sizePath (Execution.atPC input 0x12ce) = some (sizeFailed input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have heq : UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat input.size) = 0 := by
    unfold UInt256.eq
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
    simp [Ne.symm hsize]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat input.size)) := by
    rw [heq]
    decide
  simp [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeFailed, atPC,
    heq, hfalse, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_size_match (input : ByteArray) (hsize : input.size = 1000) :
    run sizePath (Execution.atPC input 0x12ce) = some (sizeMatched input) := by
  have htrue : UInt256.isTrue
      (UInt256.eq (UInt256.ofNat 1000) (UInt256.ofNat input.size)) := by
    rw [hsize]
    decide
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12dc = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2821 (by rfl)
  simp [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    hsize, htrue, hdest, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_fallback (input : ByteArray) :
    run sizeFallbackPath (sizeFailed input) = some (fallbackState input) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp [sizeFallbackPath, opAt, pushAt, wfOp, sizeFailed, fallbackState, atPC,
    hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_checkEntry (input : ByteArray) :
    run checkEntryPath (sizeMatched input) = some (loopState input 0) := by
  have hxor : UInt256.xor (UInt256.ofNat
      44046402572626160612103472728795008085361523578694645928734845681441465000289)
      (MachineState.readWord input 0) =
      UInt256.xor (MachineState.readWord input 0) (UInt256.ofNat
      44046402572626160612103472728795008085361523578694645928734845681441465000289) :=
    BooleanSelect.xor_comm _ _
  simp (config := { maxSteps := 1000000 })
    [checkEntryPath, opAt, pushAt, wfOp, sizeMatched, atPC, loopState,
    loopAcc, referenceWord, KnownInputData.fullWord, hxor, expandedFullWord,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_more (input : ByteArray) (n : Nat) (hn : n < 29) :
    run loopPath (loopState input n) = some (loopState input (n + 1)) := by
  have hdest : Decode.isValidJumpDest submissionBytecode 0x12f6 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2836 (by rfl)
  have hstart : 32 * n + 32 < 2 ^ 256 := by omega
  have hnext : 32 * n + 64 < 2 ^ 256 := by omega
  have hlt : 32 * n + 64 < 992 := by omega
  have hmod : (32 * n + 32) % 2 ^ 256 = 32 * n + 32 := Nat.mod_eq_of_lt hstart
  have hnextMod : (32 * n + 64) % 2 ^ 256 = 32 * n + 64 := Nat.mod_eq_of_lt hnext
  have hnaddr : 32 * (n + 1) = 32 * n + 32 := by omega
  have hsum : 32 + (32 * n + 32) = 32 * n + 64 := by omega
  have hcond : (UInt256.lt (UInt256.ofNat (32 * n + 64))
      (UInt256.ofNat 992)).toNat ≠ 0 := by
    unfold UInt256.lt
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, hnextMod,
      Nat.mod_eq_of_lt (by norm_num : 992 < 2 ^ 256), if_pos hlt]
    decide
  have hxor : UInt256.xor (referenceWord input)
      (MachineState.readWord input (32 * n + 32)) =
      UInt256.xor (MachineState.readWord input (32 * n + 32))
        (referenceWord input) := BooleanSelect.xor_comm _ _
  have hacc : loopAcc input (n + 1) =
      UInt256.lor (UInt256.xor (MachineState.readWord input (32 * (n + 1)))
        (referenceWord input)) (loopAcc input n) := by rw [loopAcc]
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, referenceWord, hdest, hstart,
    hnext, hmod, hnextMod, hnaddr, hsum, hlt, hcond, hxor, hacc, Word.lor_comm,
    List.exchange, Nat.add_assoc, Nat.mul_add, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_loop_last (input : ByteArray) :
    run loopPath (loopState input 29) = some (loopExitState input) := by
  have hacc : loopAcc input 30 =
      UInt256.lor (UInt256.xor (MachineState.readWord input 960)
        (referenceWord input)) (loopAcc input 29) := by
    rw [show 30 = 29 + 1 by omega, loopAcc]
  have hfalse : ¬ UInt256.isTrue
      (UInt256.lt (UInt256.ofNat 992) (UInt256.ofNat 992)) := by decide
  have hxor : UInt256.xor (referenceWord input) (MachineState.readWord input 960) =
      UInt256.xor (MachineState.readWord input 960)
        (referenceWord input) := BooleanSelect.xor_comm _ _
  simp (config := { maxSteps := 1000000 })
    [loopPath, opAt, pushAt, wfOp, loopState, loopExitState, referenceWord,
    hacc, hfalse, hxor, Word.lor_comm, List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_target :
    run tailPath (loopExitState KnownInputData.targetInput) =
      some (returnEntry KnownInputData.targetInput) := by
  have hzero : finalAcc KnownInputData.targetInput = 0 :=
    (KnownInputCompactLogic.finalAcc_zero_iff_target _
      KnownInputData.targetInput_size).2 rfl
  have hzero' : UInt256.lor
      (UInt256.xor
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput) (UInt256.ofNat 192))
        (UInt256.shiftRight (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192)))
      (loopAcc KnownInputData.targetInput 30) = 0 := by
    simpa only [finalAcc, BooleanSelect.xor_comm] using hzero
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, returnEntry, atPC,
    hzero', List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_fallback (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ KnownInputData.targetInput) :
    run tailPath (loopExitState input) = some (fallbackState input) := by
  have hneAcc : finalAcc input ≠ 0 := by
    intro hz
    exact hne ((KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1 hz)
  have htrue : UInt256.isTrue (finalAcc input) := by
    intro hz
    apply hneAcc
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue
      (UInt256.lor
        (UInt256.xor
          (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
          (UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192)))
        (loopAcc input 30)) := by
    simpa only [finalAcc, BooleanSelect.xor_comm] using htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3ee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, fallbackState, atPC,
    htrue', hdest, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_return :
    run returnPath (returnEntry KnownInputData.targetInput) =
      some (returnedState KnownInputData.targetInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, returnEntry, atPC, returnedState,
    answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

private def sound (path : List Located) {s t : State}
    (h : run path s = some t) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path rfl rfl h rfl deployAddress_not_precompile

private def gasSteps_loop (input : ByteArray) :
    GasSteps (loopState input 0) (loopExitState input) := by
  let step : ∀ n, n < 29 → GasSteps (loopState input n) (loopState input (n + 1)) :=
    fun n hn => sound loopPath (run_loop_more input n hn)
  exact (GasSteps.iterateBounded 29 step).trans
    (sound loopPath (run_loop_last input))

def gasSteps_target :
    GasSteps (initialState submissionBytecode KnownInputData.targetInput 0)
      (returnedState KnownInputData.targetInput) :=
  (Execution.gasSteps_start KnownInputData.targetInput).trans
    ((sound sizePath run_size_target).trans
      ((sound checkEntryPath (run_checkEntry KnownInputData.targetInput)).trans
        ((gasSteps_loop KnownInputData.targetInput).trans
          ((sound tailPath run_tail_target).trans
            (sound returnPath run_return)))))

def gasSteps_fallback (input : ByteArray) (hfit : CalldataFits input)
    (hne : input ≠ KnownInputData.targetInput) :
    GasSteps (initialState submissionBytecode input 0) (fallbackState input) := by
  by_cases hsize : input.size = 1000
  · exact (Execution.gasSteps_start input).trans
      ((sound sizePath (run_size_match input hsize)).trans
        ((sound checkEntryPath (run_checkEntry input)).trans
          ((gasSteps_loop input).trans
            (sound tailPath (run_tail_fallback input hsize hne)))))
  · exact (Execution.gasSteps_start input).trans
      ((sound sizePath (run_size_fail input hfit hsize)).trans
        (sound sizeFallbackPath (run_size_fallback input)))

private theorem answerMemory_read :
    MachineState.readPadded answerMemory 0 32 = ExactGuardSpec.paddedDigest := by
  unfold answerMemory storeWord
  have h := Memory.readPadded_writeBytes_same ByteArray.empty
    (Data.Bytes.natToBytesPadded ExactGuardSpec.paddedDigestWord.toNat 32) 0
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size,
    ExactGuardSpec.wordBytes_eq_paddedDigest] using h

theorem correct : Correct submissionBytecode := by
  intro input hfit
  by_cases h : input = KnownInputData.targetInput
  · subst input
    let trace := gasSteps_target
    refine ⟨trace.cost, fun gas hgas => ?_⟩
    have heval := eval_of_steps (trace.trace gas hgas) (by
      change (withGas (returnedState KnownInputData.targetInput)
        (gas - trace.cost)).isDone = true
      simp [withGas, returnedState, initialState,
        State.isDone, State.isHalted, State.isRunning])
    rw [State.toResult_returned _ (by rfl)] at heval
    change Eval (withGas
      (initialState submissionBytecode KnownInputData.targetInput 0) gas)
      (.returned (MachineState.readPadded answerMemory 0 32)) at heval
    rw [answerMemory_read, ← ExactGuardSpec.spec_targetInput_eq] at heval
    simpa [GasCost.withGas_initialState_zero] using heval
  · exact StackCorrect.correct input hfit (gasSteps_fallback input hfit h)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
