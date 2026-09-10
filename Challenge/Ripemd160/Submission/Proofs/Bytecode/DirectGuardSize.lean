import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The calldata-size check. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

/-- `UInt256.eq` is `if a.toNat = b.toNat then 1 else 0`, and both operands are
below `2 ^ 256`, so the test reduces to the underlying `Nat` comparison. -/
private theorem size_eq_zero (input : ByteArray) (k : Nat)
    (hlt : input.size < 2 ^ 256) (hk : k < 2 ^ 256) (hne : input.size ≠ k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hne]

private theorem size_eq_one (input : ByteArray) (k : Nat)
    (heq : input.size = k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 1 := by
  rw [heq]
  unfold UInt256.eq
  simp

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) (hsize256 : input.size ≠ 376) (hshort : input.size ≠ 256) :
    run sizePath (Execution.atPC input 0x0) = some (fallbackState input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have eshort := size_eq_zero input 256 hlt (by norm_num) hshort
  have e256 := size_eq_zero input 376 hlt (by norm_num) hsize256
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) hsize
  have hdest : Decode.isValidJumpDest submissionBytecode 0x168 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 200 (by rfl)
  simp (config := { decide := true })
    [sizePath, opAt, pushAt, wfOp, Execution.atPC, fallbackState, atPC,
    eshort, e256, e1000, hdest, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_match (input : ByteArray) (hsize : input.size = 1000) :
    run sizePath (Execution.atPC input 0x0) = some (sizeMatched input) := by
  have hlt : input.size < 2 ^ 256 := by rw [hsize]; norm_num
  have eshort := size_eq_zero input 256 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e256 := size_eq_zero input 376 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e1000 := size_eq_one input 1000 hsize
  simp (config := { decide := true })
    [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    eshort, e256, e1000, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The memo's size.  It reaches the SAME state as 1000: the merged test ORs the
two equalities, and the first-word test at idx 113-124 separates them after. -/
theorem run_size_match_256 (input : ByteArray) (hsize : input.size = 376) :
    run sizePath (Execution.atPC input 0x0) = some (sizeMatched input) := by
  have hlt : input.size < 2 ^ 256 := by rw [hsize]; norm_num
  have eshort := size_eq_zero input 256 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e256 := size_eq_one input 376 hsize
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) (by rw [hsize]; norm_num)
  simp (config := { decide := true })
    [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    eshort, e256, e1000, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_match_short (input : ByteArray) (hsize : input.size = 256) :
    run sizePath (Execution.atPC input 0x0) = some (sizeMatched input) := by
  have hlt : input.size < 2 ^ 256 := by rw [hsize]; norm_num
  have eshort := size_eq_one input 256 hsize
  have e256 := size_eq_zero input 376 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) (by rw [hsize]; norm_num)
  simp (config := { decide := true })
    [sizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    eshort, e256, e1000, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
