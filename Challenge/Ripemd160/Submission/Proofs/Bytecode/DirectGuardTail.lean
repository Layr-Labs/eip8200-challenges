import Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64RepeatMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardLoop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The final word, the two exits and the stored answer. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

/-- `OR` with the spent zero counter keeps the accumulator. -/
theorem lor_zero_toNat (a : UInt256) :
    (UInt256.lor a (UInt256.ofNat 0)).toNat = a.toNat := by
  rw [Challenge.EvmProof.Word.word_toNat_lor, Challenge.EvmProof.Word.word_toNat_ofNat]
  simp

theorem fullWord_toNat : KnownInputData.fullWord.toNat =
    0x6161616161616161616161616161616161616161616161616161616161616161 := by
  unfold KnownInputData.fullWord
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  norm_num

/-- The anchor word `0x6161…61` is odd, so it is invertible modulo `2^256`. -/
theorem fullWord_inverse :
    (KnownInputData.fullWord.toNat *
      1193732878735218509521350360914308328384226646037531588035645195957867315873) % 2 ^ 256 = 1 := by
  rw [fullWord_toNat]
  norm_num

theorem eq_zero_of_mul_inv (x f inv : Nat) (hx : x < 2 ^ 256) (hinv : (f * inv) % 2 ^ 256 = 1)
    (h : (x * f) % 2 ^ 256 = 0) : x = 0 := by
  have key : x % 2 ^ 256 = ((x * f) % 2 ^ 256 * inv) % 2 ^ 256 := by
    rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, hinv, Nat.mul_one, Nat.mod_mod]
  rw [h, Nat.zero_mul, Nat.zero_mod, Nat.mod_eq_of_lt hx] at key
  exact key

theorem word_toNat_mul (x y : UInt256) : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ 256 := by
  show (x.val * y.val).val = _
  rw [Fin.val_mul]
  rfl

/-- Scaling by the odd anchor word keeps a nonzero word nonzero. -/
theorem mul_fullWord_toNat_ne_zero (x : UInt256) (hx : x.toNat ≠ 0) :
    (x * KnownInputData.fullWord).toNat ≠ 0 := by
  intro hz
  rw [word_toNat_mul] at hz
  exact hx (eq_zero_of_mul_inv x.toNat KnownInputData.fullWord.toNat _ x.val.isLt fullWord_inverse hz)

theorem condWord_isTrue (acc : UInt256) (hacc : acc ≠ 0) :
    UInt256.isTrue (UInt256.lor acc (UInt256.ofNat 0) * KnownInputData.fullWord) := by
  apply mul_fullWord_toNat_ne_zero
  rw [lor_zero_toNat]
  intro hz
  apply hacc
  apply Challenge.EvmProof.Word.word_ext
  simpa using hz

theorem condWord_zero (r : UInt256) :
    UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) * r = UInt256.ofNat 0 := by
  apply Challenge.EvmProof.Word.word_ext
  rw [word_toNat_mul, lor_zero_toNat, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod,
    Nat.zero_mul, Nat.zero_mod]

private theorem tail_push_pc : Artifact.submissionArtifact.instructionPC 5386 = 9632 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem tail_jump_pc : Artifact.submissionArtifact.instructionPC 5387 = 9635 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
private theorem valid_terminal_miss : Decode.isValidJumpDest submissionBytecode 9662 = true := by
  have hp : Artifact.submissionArtifact.instructionPC 5394 = 9662 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have h := Artifact.submissionArtifact.isValidJumpDest_index 5394 (by rfl)
  rw [hp] at h
  exact h

theorem run_tail_target :
    run tailPath (loopExitState KnownInputData.targetInput) =
      some (returnHopState KnownInputData.targetInput) := by
  have hm := PcSeedMath.mismatch_target
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, returnHopState, returnCells,
    tail_push_pc, tail_jump_pc, hm, UInt256.isTrue,
    Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
    Challenge.EvmProof.DataStepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_return_hop (input : ByteArray) :
    run returnHopPath (returnHopState input) = some (returnEntry input) := by rfl

theorem run_fallback_clear (input : ByteArray) :
    run fallbackPath (tailDivertState input) = some (fallbackState input) := by
  have hdestpc : Artifact.submissionArtifact.instructionPC 5394 = 9662 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hzeropc : Artifact.submissionArtifact.instructionPC 5395 = 9663 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hpushpc : Artifact.submissionArtifact.instructionPC 5396 = 9664 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hjumppc : Artifact.submissionArtifact.instructionPC 5397 = 9666 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  simp (config := { maxSteps := 1000000 })
    [fallbackPath, entryDest, opAt, pushAt, wfOp, tailDivertState, fallbackState,
    StackTail.append, genericMissCells, spentCells, returnCells, atPC, PatternedScan.stS,
    hdestpc, hzeropc, hpushpc, hjumppc, Artifact.validJumpDest_3ee, List.exchange,
    Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
    Challenge.EvmProof.DataStepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_divert_low (input : ByteArray) (hsize : input.size = 1000)
    (hcond : Low64RepeatMath.condition input = 0)
    (hne : input ≠ KnownInputData.targetInput) :
    run tailPath (loopExitState input) = some (tailDivertState input) := by
  have hm : (PcSeedRaw.mismatch input).toNat ≠ 0 := by
    intro hz
    exact hne (PcSeedMath.mismatch_zero_target input hsize hcond (Word.word_ext hz))
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, tailDivertState, returnCells,
      tail_push_pc, tail_jump_pc, hm, UInt256.isTrue, valid_terminal_miss,
      Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
      Challenge.EvmProof.DataStepper.runInstr,
      Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

@[simp] private theorem terminal_pc_5412 : Artifact.submissionArtifact.instructionPC 5388 = 9636 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem terminal_pc_5413 : Artifact.submissionArtifact.instructionPC 5389 = 9657 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem terminal_pc_5414 : Artifact.submissionArtifact.instructionPC 5390 = 9658 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem terminal_pc_5415 : Artifact.submissionArtifact.instructionPC 5391 = 9659 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem terminal_pc_5416 : Artifact.submissionArtifact.instructionPC 5392 = 9660 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
@[simp] private theorem terminal_pc_5417 : Artifact.submissionArtifact.instructionPC 5393 = 9661 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl

theorem run_return_store (input : ByteArray) :
    run returnPath (returnEntry input) = some (storedReturnState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, returnEntry, returnCells, atPC, PatternedScan.stS, storedReturnState,
    initialState, answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
    Challenge.EvmProof.DataStepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_return_finish (input : ByteArray) :
    run returnFinishPath (sizedReturnState input) = some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnFinishPath, opAt, pushAt, wfOp, sizedReturnState, storedReturnState,
    returnedState, returnCells, initialState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
    Challenge.EvmProof.DataStepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_direct_return (input : ByteArray) :
    GasSteps (returnEntry input) (returnedState input) := by
  have gs := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    returnPath (by rfl) (by rfl) (run_return_store input) (by rfl)
    deployAddress_not_precompile
  have hd := Artifact.submissionArtifact.decodeAt_op_index 5391 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedReturnState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 5391 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hop : (storedReturnState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedReturnState input) 5391
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop
    (by simp [storedReturnState, returnCells]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (storedReturnState input) (sizedReturnState input) := by
    simpa [storedReturnState, sizedReturnState, returnCells, initialState,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    returnFinishPath (by rfl) (by rfl) (run_return_finish input) (by rfl)
    deployAddress_not_precompile
  exact gs.trans (gm.trans gf)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
