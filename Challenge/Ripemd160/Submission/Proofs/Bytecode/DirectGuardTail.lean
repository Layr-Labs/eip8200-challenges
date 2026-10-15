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

/-- A zero accumulator takes the `ISZERO PUSH2 4709 JUMPI` exit to the answer block. Stated for any input
with a zero accumulator; the `JUMPI` runs as its own step (`stepG_jumpi_taken`), since one `simp` over the
whole path does not finish inside the memory budget. -/
theorem run_tail_zero (input : ByteArray) (hz : reverseAcc input 10 = UInt256.ofNat 0) :
    run tailPath (loopExitState input) = some (returnHopState input) := by
  have hiz0 : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
    unfold UInt256.isZero
    exact if_pos (by decide)
  have hpre : run (tailPath.take 2) (loopExitState input) =
      some (stG input 244 (UInt256.ofNat 4709 :: UInt256.ofNat 1 :: spentCells input)) := by
    simp (config := { maxSteps := 1000000 })
      [tailPath, opAt, pushAt, wfOp, loopExitState, stG, spentCells, atPC,
      hz, hiz0, List.exchange,
      Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
      Challenge.EvmProof.DataStepper.runInstr,
      Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
  have hpc : (stG input 244 (UInt256.ofNat 4709 :: UInt256.ofNat 1 :: spentCells input)).pc.toNat =
      Artifact.submissionArtifact.instructionPC 153 := by
    rw [pc_direct_77]; rfl
  have hjump : run (tailPath.drop 2)
      (stG input 244 (UInt256.ofNat 4709 :: UInt256.ofNat 1 :: spentCells input)) =
      some (returnHopState input) :=
    blockOf (opAt 153 .JUMPI) hpc
      (stepG_jumpi_taken input 244 4709 (UInt256.ofNat 1) (spentCells input)
        (by simp [spentCells]) (by norm_num) (by decide) Artifact.validJumpDest_4708)
  rw [← List.take_append_drop 2 tailPath]
  exact Challenge.EvmProof.DataStepper.runLocatedBlock_append _ _ _ _ _ hpre rfl hjump

theorem run_tail_target :
    run tailPath (loopExitState KnownInputData.targetInput) =
      some (returnHopState KnownInputData.targetInput) :=
  run_tail_zero _ reverseAcc_target_zero

/-- The taken `JUMPI` lands on the answer block's `JUMPDEST` 4709 in the tail. -/
theorem run_return_hop (input : ByteArray) :
    run returnHopPath (returnHopState input) = some (returnEntry input) := by
  have p3502 : Artifact.submissionArtifact.instructionPC 3474 = 4709 := Artifact.cgPc3502
  change run [opAt 3474 .JUMPDEST] (PatternedScan.stS input 4709 (spentCells input)) =
    some (PatternedScan.stS input 4710 (spentCells input))
  exact PatternedScan.blockOfS _ (PatternedScan.pcFactS input 3474 4709 _ (by norm_num) p3502)
    (PatternedScan.stepS_jumpdest input 4709 _ (by simp [spentCells]) (by norm_num))

/-- A nonzero accumulator diverts to the generic arm with a two-word suffix. -/
theorem run_tail_divert_acc (input : ByteArray) (hneAcc : reverseAcc input 10 ≠ 0) :
    run tailPath (loopExitState input) = some (tailDivertState input) := by
  have hiz : UInt256.isZero (reverseAcc input 10) = UInt256.ofNat 0 := by
    unfold UInt256.isZero
    exact if_neg (fun hn => hneAcc (Challenge.EvmProof.Word.word_ext hn))
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, tailDivertState, spentCells, atPC,
    hiz, List.exchange, UInt256.isTrue,
    Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
    Challenge.EvmProof.DataStepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The generic arm's entry `JUMPDEST`. -/
theorem run_fallback_clear (input : ByteArray) :
    run fallbackPath (tailDivertState input) = some (fallbackState input) := by
  simp (config := { maxSteps := 1000000 })
    [fallbackPath, entryDest, opAt, pushAt, wfOp, tailDivertState, fallbackState,
    StackTail.append, spentCells, atPC,
    List.exchange,
    Challenge.EvmProof.DataStepper.runLocatedBlock, Challenge.EvmProof.DataStepper.runLocated,
    Challenge.EvmProof.DataStepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_divert (input : ByteArray) (hsize : input.size = 1000)
    (href : referenceWord input = KnownInputData.fullWord)
    (hne : input ≠ KnownInputData.targetInput) :
    run tailPath (loopExitState input) = some (tailDivertState input) :=
  run_tail_divert_acc input (fun hz => hne (reverseAcc_zero_target input hsize href hz))

theorem run_return_store (input : ByteArray) :
    run returnPath (returnEntry input) = some (storedReturnState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, returnEntry, spentCells, atPC, storedReturnState,
    answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
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
    returnedState, spentCells, initialState, State.activeWordsAfterUInt256,
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
  have hd := Artifact.submissionArtifact.decodeAt_op_index 3481 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (storedReturnState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 3478 := by
    rw [Artifact.cjPc58]; rfl
  have hop : (storedReturnState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (storedReturnState input) 3481
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop
    (by simp [storedReturnState, spentCells]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (storedReturnState input) (sizedReturnState input) := by
    simpa [storedReturnState, sizedReturnState, spentCells, initialState,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    returnFinishPath (by rfl) (by rfl) (run_return_finish input) (by rfl)
    deployAddress_not_precompile
  exact gs.trans (gm.trans gf)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
