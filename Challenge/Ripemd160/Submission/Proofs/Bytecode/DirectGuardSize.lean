import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortSizePrefix

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The calldata-size check. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def guardEntry (input : ByteArray) : State := atPC input 4792

def firstByte (input : ByteArray) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList 0).toNat

/-- `UInt256.eq` is `if a.toNat = b.toNat then 1 else 0`, and both operands are
below `2 ^ 256`, so the test reduces to the underlying `Nat` comparison. -/
theorem size_eq_zero (input : ByteArray) (k : Nat)
    (hlt : input.size < 2 ^ 256) (hk : k < 2 ^ 256) (hne : input.size ≠ k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 0 := by
  unfold UInt256.eq
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hne]

theorem size_eq_one (input : ByteArray) (k : Nat)
    (heq : input.size = k) :
    UInt256.eq (UInt256.ofNat k) (UInt256.ofNat input.size) = UInt256.ofNat 1 := by
  rw [heq]
  unfold UInt256.eq
  simp

theorem run_size_fail_legacy (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) (hsize256 : input.size ≠ 376) (hshort : input.size ≠ 256) :
    run sizePath (Execution.atPC input 8) = some (guardEntry input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have eshort := size_eq_zero input 256 hlt (by norm_num) hshort
  have e256 := size_eq_zero input 376 hlt (by norm_num) hsize256
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) hsize
  change run sizePath (PatternedScan.stS input 8 []) =
    some (PatternedScan.stS input 4792 [])
  -- rw idiom rather than term mode: the term form forces instructionPC 3839 and
  -- submissionBytecode into definitional equality with the literals, which ran
  -- past 800s at 18 GB on the other base.  Same statement, cheap elaboration.
  have hpc4131 : Artifact.submissionArtifact.instructionPC 3839 = 4792 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hdest : Decode.isValidJumpDest submissionBytecode 4792 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 3839 (by rfl)
    rw [hpc4131] at h
    exact h
  have hprefix :
      run
          [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
           opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
           opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
           opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO]
        (PatternedScan.stS input 8 []) =
      some (PatternedScan.stS input 26 [UInt256.ofNat 1]) := by
    simp (config := { decide := true })
      [opAt, pushAt, wfOp, PatternedScan.stS,
       eshort, e256, e1000, UInt256.lor, UInt256.isZero, List.exchange,
       Challenge.EvmProof.Stepper.runLocatedBlock,
       Challenge.EvmProof.Stepper.runLocated,
       Challenge.EvmProof.Stepper.runInstr,
       Challenge.EvmProof.Word.literal_eq_ofNat,
       Challenge.EvmProof.Word.succ_ofNat_mod,
       Challenge.EvmProof.Word.ofNat_add_mod,
       Challenge.EvmProof.Word.word_toNat_ofNat]
  have hpush :
      run [pushAt 17 2 4792] (PatternedScan.stS input 26 [UInt256.ofNat 1]) =
        some (PatternedScan.stS input 29 [UInt256.ofNat 4792, UInt256.ofNat 1]) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 17 26 _ (by norm_num) pc_classifier_112)
      (PatternedScan.stepS_push input 26 2 4792 [UInt256.ofNat 1]
        (by norm_num) (by decide) (by decide) (by norm_num))
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have hjump :
      run [opAt 18 .JUMPI]
          (PatternedScan.stS input 29 [UInt256.ofNat 4792, UInt256.ofNat 1]) =
        some (PatternedScan.stS input 4792 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 18 29 _ (by norm_num) pc_classifier_113)
      (PatternedScan.stepS_jumpi_taken input 29 4792 4792 (UInt256.ofNat 1) []
        (by norm_num) (by norm_num) rfl htrue hdest)
  have hprefix_push :
      run
          [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
           opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
           opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
           opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO,
           pushAt 17 2 4792]
        (PatternedScan.stS input 8 []) =
      some (PatternedScan.stS input 29 [UInt256.ofNat 4792, UInt256.ofNat 1]) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
       opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
       opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
       opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO]
      [pushAt 17 2 4792] _ _ _ hprefix rfl hpush
  have hfull :
      run
          [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
           opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
           opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
           opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO,
           pushAt 17 2 4792, opAt 18 .JUMPI]
        (PatternedScan.stS input 8 []) =
      some (PatternedScan.stS input 4792 []) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
       opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
       opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
       opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO,
       pushAt 17 2 4792]
      [opAt 18 .JUMPI] _ _ _ hprefix_push rfl hjump
  simpa only [sizePath] using hfull

theorem run_size_match_legacy (input : ByteArray) (hsize : input.size = 1000) :
    run sizePath (Execution.atPC input 8) = some (sizeMatched input) := by
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
theorem run_size_match_256_legacy (input : ByteArray) (hsize : input.size = 376) :
    run sizePath (Execution.atPC input 8) = some (sizeMatched input) := by
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

theorem run_size_match_short_legacy (input : ByteArray) (hsize : input.size = 256) :
    run sizePath (Execution.atPC input 8) = some (sizeMatched input) := by
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

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) (hsize376 : input.size ≠ 376) (hsize256 : input.size ≠ 256) :
    run (sizeDispatchPath input) (Execution.atPC input 0) = some (guardEntry input) := by
  by_cases hsmall : input.size < 255
  · simpa only [sizeDispatchPath, if_pos hsmall, guardEntry] using run_short_size_taken input hsmall
  · simp only [sizeDispatchPath, if_neg hsmall]
    exact Stepper.runLocatedBlock_append shortSizePath sizePath _ _ _
      (run_short_size_fall input hfit hsmall) rfl
      (run_size_fail_legacy input hfit hsize hsize376 hsize256)

theorem run_size_match (input : ByteArray) (hsize : input.size = 1000) :
    run (sizeDispatchPath input) (Execution.atPC input 0) = some (sizeMatched input) := by
  have hfit : CalldataFits input := by change input.size < 2 ^ 64; rw [hsize]; norm_num
  have hlarge : ¬ input.size < 255 := by omega
  simp only [sizeDispatchPath, if_neg hlarge]
  exact Stepper.runLocatedBlock_append shortSizePath sizePath _ _ _
    (run_short_size_fall input hfit hlarge) rfl (run_size_match_legacy input hsize)

theorem run_size_match_256 (input : ByteArray) (hsize : input.size = 376) :
    run (sizeDispatchPath input) (Execution.atPC input 0) = some (sizeMatched input) := by
  have hfit : CalldataFits input := by change input.size < 2 ^ 64; rw [hsize]; norm_num
  have hlarge : ¬ input.size < 255 := by omega
  simp only [sizeDispatchPath, if_neg hlarge]
  exact Stepper.runLocatedBlock_append shortSizePath sizePath _ _ _
    (run_short_size_fall input hfit hlarge) rfl (run_size_match_256_legacy input hsize)

theorem run_size_match_short (input : ByteArray) (hsize : input.size = 256) :
    run (sizeDispatchPath input) (Execution.atPC input 0) = some (sizeMatched input) := by
  have hfit : CalldataFits input := by change input.size < 2 ^ 64; rw [hsize]; norm_num
  have hlarge : ¬ input.size < 255 := by omega
  simp only [sizeDispatchPath, if_neg hlarge]
  exact Stepper.runLocatedBlock_append shortSizePath sizePath _ _ _
    (run_short_size_fall input hfit hlarge) rfl (run_size_match_short_legacy input hsize)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
