import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The calldata-size check. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

def guardEntry (input : ByteArray) : State := atPC input 4807

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

theorem run_size_fail_large (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) (hsize256 : input.size ≠ 376) (hshort : input.size ≠ 256) :
    run largeSizePath (Execution.atPC input 8) = some (guardEntry input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  have eshort := size_eq_zero input 256 hlt (by norm_num) hshort
  have e256 := size_eq_zero input 376 hlt (by norm_num) hsize256
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) hsize
  change run largeSizePath (PatternedScan.stS input 8 []) =
    some (PatternedScan.stS input 4807 [])
  -- rw idiom rather than term mode: the term form forces instructionPC 3890 and
  -- submissionBytecode into definitional equality with the literals, which ran
  -- past 800s at 18 GB on the other base.  Same statement, cheap elaboration.
  have hpc4131 : Artifact.submissionArtifact.instructionPC 3890 = 4807 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have hdest : Decode.isValidJumpDest submissionBytecode 4807 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 3890 (by rfl)
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
      run [pushAt 17 2 4807] (PatternedScan.stS input 26 [UInt256.ofNat 1]) =
        some (PatternedScan.stS input 29 [UInt256.ofNat 4807, UInt256.ofNat 1]) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 17 26 _ (by norm_num) pc_classifier_112)
      (PatternedScan.stepS_push input 26 2 4807 [UInt256.ofNat 1]
        (by norm_num) (by decide) (by decide) (by norm_num))
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have hjump :
      run [opAt 18 .JUMPI]
          (PatternedScan.stS input 29 [UInt256.ofNat 4807, UInt256.ofNat 1]) =
        some (PatternedScan.stS input 4807 []) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 18 29 _ (by norm_num) pc_classifier_113)
      (PatternedScan.stepS_jumpi_taken input 29 4807 4807 (UInt256.ofNat 1) []
        (by norm_num) (by norm_num) rfl htrue hdest)
  have hprefix_push :
      run
          [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
           opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
           opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
           opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO,
           pushAt 17 2 4807]
        (PatternedScan.stS input 8 []) =
      some (PatternedScan.stS input 29 [UInt256.ofNat 4807, UInt256.ofNat 1]) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
       opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
       opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
       opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO]
      [pushAt 17 2 4807] _ _ _ hprefix rfl hpush
  have hfull :
      run
          [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
           opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
           opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
           opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO,
           pushAt 17 2 4807, opAt 18 .JUMPI]
        (PatternedScan.stS input 8 []) =
      some (PatternedScan.stS input 4807 []) := by
    exact Challenge.EvmProof.Stepper.runLocatedBlock_append
      [opAt 5 .CALLDATASIZE, pushAt 6 2 256, opAt 7 .EQ,
       opAt 8 .CALLDATASIZE, pushAt 9 2 376, opAt 10 .EQ,
       opAt 11 .CALLDATASIZE, pushAt 12 2 1000,
       opAt 13 .EQ, opAt 14 .OR, opAt 15 .OR, opAt 16 .ISZERO,
       pushAt 17 2 4807]
      [opAt 18 .JUMPI] _ _ _ hprefix_push rfl hjump
  simpa only [largeSizePath] using hfull

theorem run_size_match_large (input : ByteArray) (hsize : input.size = 1000) :
    run largeSizePath (Execution.atPC input 8) = some (sizeMatched input) := by
  have hlt : input.size < 2 ^ 256 := by rw [hsize]; norm_num
  have eshort := size_eq_zero input 256 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e256 := size_eq_zero input 376 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e1000 := size_eq_one input 1000 hsize
  simp (config := { decide := true })
    [largeSizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    eshort, e256, e1000, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

/-- The memo's size.  It reaches the SAME state as 1000: the merged test ORs the
two equalities, and the first-word test at idx 113-124 separates them after. -/
theorem run_size_match_256_large (input : ByteArray) (hsize : input.size = 376) :
    run largeSizePath (Execution.atPC input 8) = some (sizeMatched input) := by
  have hlt : input.size < 2 ^ 256 := by rw [hsize]; norm_num
  have eshort := size_eq_zero input 256 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e256 := size_eq_one input 376 hsize
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) (by rw [hsize]; norm_num)
  simp (config := { decide := true })
    [largeSizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    eshort, e256, e1000, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_size_match_short_large (input : ByteArray) (hsize : input.size = 256) :
    run largeSizePath (Execution.atPC input 8) = some (sizeMatched input) := by
  have hlt : input.size < 2 ^ 256 := by rw [hsize]; norm_num
  have eshort := size_eq_one input 256 hsize
  have e256 := size_eq_zero input 376 hlt (by norm_num) (by rw [hsize]; norm_num)
  have e1000 := size_eq_zero input 1000 hlt (by norm_num) (by rw [hsize]; norm_num)
  simp (config := { decide := true })
    [largeSizePath, opAt, pushAt, wfOp, Execution.atPC, sizeMatched, atPC,
    eshort, e256, e1000, UInt256.isTrue, UInt256.lor, UInt256.isZero, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem run_sizePrelude (input : ByteArray) (hfit : CalldataFits input) :
    run sizePrelude (Execution.atPC input 0) =
      some (if input.size < 129 then guardEntry input else Execution.atPC input 8) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  let c := UInt256.gt (UInt256.ofNat 129) (UInt256.ofNat input.size)
  have hgt : c = (if input.size < 129 then UInt256.ofNat 1 else UInt256.ofNat 0) := by
    unfold c UInt256.gt
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num : 129 < 2 ^ 256), Nat.mod_eq_of_lt hlt]
  have hp0 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hp1 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hp2 : Artifact.submissionArtifact.instructionPC 2 = 3 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hp3 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hp4 : Artifact.submissionArtifact.instructionPC 4 = 7 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hdpc : Artifact.submissionArtifact.instructionPC 3890 = 4807 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
  have hdest : Decode.isValidJumpDest submissionBytecode 4807 = true := by
    have h := Artifact.submissionArtifact.isValidJumpDest_index 3890 (by rfl)
    rw [hdpc] at h
    exact h
  change run sizePrelude (PatternedScan.stS input 0 []) =
    some (if input.size < 129 then PatternedScan.stS input 4807 [] else PatternedScan.stS input 8 [])
  have a : run [opAt 0 .CALLDATASIZE] (PatternedScan.stS input 0 []) =
      some (PatternedScan.stS input 1 [UInt256.ofNat input.size]) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 0 0 _ (by norm_num) hp0)
      (PatternedScan.stepS_calldatasize input 0 [] (by simp) (by norm_num))
  have b : run [pushAt 1 1 129] (PatternedScan.stS input 1 [UInt256.ofNat input.size]) =
      some (PatternedScan.stS input 3 [UInt256.ofNat 129, UInt256.ofNat input.size]) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 1 1 _ (by norm_num) hp1)
      (PatternedScan.stepS_push input 1 1 129 [UInt256.ofNat input.size]
        (by simp) (by decide) (by decide) (by norm_num))
  have cc : run [opAt 2 .GT] (PatternedScan.stS input 3 [UInt256.ofNat 129, UInt256.ofNat input.size]) =
      some (PatternedScan.stS input 4 [c]) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 2 3 _ (by norm_num) hp2)
      (PatternedScan.stepS_gt input 3 (UInt256.ofNat 129) (UInt256.ofNat input.size) []
        (by simp) (by norm_num))
  have d : run [pushAt 3 2 4807] (PatternedScan.stS input 4 [c]) =
      some (PatternedScan.stS input 7 [UInt256.ofNat 4807, c]) := by
    exact PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3 4 _ (by norm_num) hp3)
      (PatternedScan.stepS_push input 4 2 4807 [c]
        (by simp) (by decide) (by decide) (by norm_num))
  have e : run [opAt 4 .JUMPI] (PatternedScan.stS input 7 [UInt256.ofNat 4807, c]) =
      some (if input.size < 129 then PatternedScan.stS input 4807 [] else PatternedScan.stS input 8 []) := by
    by_cases hs : input.size < 129
    · rw [if_pos hs]
      have hc : UInt256.isTrue c := by rw [hgt, if_pos hs]; decide
      exact PatternedScan.blockOfS _
        (PatternedScan.pcFactS input 4 7 _ (by norm_num) hp4)
        (PatternedScan.stepS_jumpi_taken input 7 4807 4807 c []
          (by simp) (by norm_num) rfl hc hdest)
    · rw [if_neg hs]
      have hc : ¬ UInt256.isTrue c := by rw [hgt, if_neg hs]; decide
      exact PatternedScan.blockOfS _
        (PatternedScan.pcFactS input 4 7 _ (by norm_num) hp4)
        (PatternedScan.stepS_jumpi_fall input 7 4807 c []
          (by simp) (by norm_num) hc)
  have ab := Stepper.runLocatedBlock_append [opAt 0 .CALLDATASIZE] [pushAt 1 1 129] _ _ _ a rfl b
  have abc := Stepper.runLocatedBlock_append ([opAt 0 .CALLDATASIZE] ++ [pushAt 1 1 129]) [opAt 2 .GT] _ _ _ ab rfl cc
  have abcd := Stepper.runLocatedBlock_append (([opAt 0 .CALLDATASIZE] ++ [pushAt 1 1 129]) ++ [opAt 2 .GT]) [pushAt 3 2 4807] _ _ _ abc rfl d
  have abcde := Stepper.runLocatedBlock_append ((([opAt 0 .CALLDATASIZE] ++ [pushAt 1 1 129]) ++ [opAt 2 .GT]) ++ [pushAt 3 2 4807]) [opAt 4 .JUMPI] _ _ _ abcd rfl e
  simpa only [sizePrelude, List.cons_append, List.nil_append] using abcde

theorem run_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 1000) (h376 : input.size ≠ 376) (h256 : input.size ≠ 256) :
    run (sizePath input) (Execution.atPC input 0) = some (guardEntry input) := by
  have hp := run_sizePrelude input hfit
  by_cases hs : input.size < 129
  · simpa only [sizePath, if_pos hs, List.append_nil] using hp
  · rw [if_neg hs] at hp
    have h := Stepper.runLocatedBlock_append sizePrelude largeSizePath _ _ _ hp rfl
      (run_size_fail_large input hfit hsize h376 h256)
    simpa only [sizePath, if_neg hs] using h

theorem run_size_match (input : ByteArray) (hsize : input.size = 1000) :
    run (sizePath input) (Execution.atPC input 0) = some (sizeMatched input) := by
  have hf : CalldataFits input := by unfold CalldataFits; rw [hsize]; norm_num
  have hs : ¬ input.size < 129 := by omega
  have hp := run_sizePrelude input hf
  rw [if_neg hs] at hp
  have h := Stepper.runLocatedBlock_append sizePrelude largeSizePath _ _ _ hp rfl
    (run_size_match_large input hsize)
  simpa only [sizePath, if_neg hs] using h

theorem run_size_match_256 (input : ByteArray) (hsize : input.size = 376) :
    run (sizePath input) (Execution.atPC input 0) = some (sizeMatched input) := by
  have hf : CalldataFits input := by unfold CalldataFits; rw [hsize]; norm_num
  have hs : ¬ input.size < 129 := by omega
  have hp := run_sizePrelude input hf
  rw [if_neg hs] at hp
  have h := Stepper.runLocatedBlock_append sizePrelude largeSizePath _ _ _ hp rfl
    (run_size_match_256_large input hsize)
  simpa only [sizePath, if_neg hs] using h

theorem run_size_match_short (input : ByteArray) (hsize : input.size = 256) :
    run (sizePath input) (Execution.atPC input 0) = some (sizeMatched input) := by
  have hf : CalldataFits input := by unfold CalldataFits; rw [hsize]; norm_num
  have hs : ¬ input.size < 129 := by omega
  have hp := run_sizePrelude input hf
  rw [if_neg hs] at hp
  have h := Stepper.runLocatedBlock_append sizePrelude largeSizePath _ _ _ hp rfl
    (run_size_match_short_large input hsize)
  simpa only [sizePath, if_neg hs] using h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
