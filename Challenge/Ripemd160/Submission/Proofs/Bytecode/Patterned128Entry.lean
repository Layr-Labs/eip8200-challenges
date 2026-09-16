import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLengthLookup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.J2EntryWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionEntryPrelude
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-!
# The patterned guard

Entered at pc 4827 when the first calldata byte is 7, or when a short or
1000-byte input does not start with the repeated `0x61` word.  A size mask sends the
eleven short patterned lengths to the scanner; a second test sends 256, 376 and
1000.  Every other length falls through into the tiny-input arm.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

abbrev Located := DirectGuard.Located

private def sound (path : List Located) {s t : State}
    (h : DirectGuard.run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 67 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 110 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 67 (by rfl)

private theorem calldatasize_step (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

/-! ## Program counters in the guard window -/

private theorem pc3836 : Artifact.submissionArtifact.instructionPC 3683 = 4827 := J2EntryWindow.pc 0
private theorem pc3837 : Artifact.submissionArtifact.instructionPC 3684 = 4828 := J2EntryWindow.pc 1
private theorem pc3843 : Artifact.submissionArtifact.instructionPC 3690 = 4853 := J2EntryWindow.pc 7
private theorem packedPC3735 : Artifact.submissionArtifact.instructionPC 3691 = 4854 := J2EntryWindow.pc 8
private theorem packedPC3736 : Artifact.submissionArtifact.instructionPC 3692 = 4857 := J2EntryWindow.pc 9
private theorem packedPC3737 : Artifact.submissionArtifact.instructionPC 3693 = 4863 := J2EntryWindow.pc 10
private theorem packedPC3738 : Artifact.submissionArtifact.instructionPC 3694 = 4864 := J2EntryWindow.pc 11
private theorem packedPC3739 : Artifact.submissionArtifact.instructionPC 3695 = 4866 := J2EntryWindow.pc 12
private theorem packedPC3740 : Artifact.submissionArtifact.instructionPC 3696 = 4867 := J2EntryWindow.pc 13
private theorem packedPC3741 : Artifact.submissionArtifact.instructionPC 3697 = 4868 := J2EntryWindow.pc 14
private theorem packedPC3742 : Artifact.submissionArtifact.instructionPC 3698 = 4869 := J2EntryWindow.pc 15
private theorem packedPC3743 : Artifact.submissionArtifact.instructionPC 3699 = 4870 := J2EntryWindow.pc 16
private theorem packedPC3744 : Artifact.submissionArtifact.instructionPC 3700 = 4871 := J2EntryWindow.pc 17
private theorem packedPC3745 : Artifact.submissionArtifact.instructionPC 3701 = 4873 := J2EntryWindow.pc 18

@[simp] private theorem sizeHitPC3838 : Artifact.submissionArtifact.instructionPC 3685 = 4830 :=
  J2EntryWindow.pc 2
@[simp] private theorem sizeHitPC3839 : Artifact.submissionArtifact.instructionPC 3686 = 4848 :=
  J2EntryWindow.pc 3
@[simp] private theorem sizeHitPC3840 : Artifact.submissionArtifact.instructionPC 3687 = 4849 :=
  J2EntryWindow.pc 4
@[simp] private theorem sizeHitPC3841 : Artifact.submissionArtifact.instructionPC 3688 = 4850 :=
  J2EntryWindow.pc 5
@[simp] private theorem sizeHitPC3842 : Artifact.submissionArtifact.instructionPC 3689 = 4851 :=
  J2EntryWindow.pc 6

/-! ## The size mask -/

private def maskEntry : List Located :=
  [DirectGuard.opAt 3683 .JUMPDEST (by exact J2EntryWindow.get 0)]

private def sizePrefix : List Located :=
  [DirectGuard.pushAt 3684 1 1 (by exact J2EntryWindow.get 1),
   DirectGuard.pushAt 3685 17 342276208914615837337402008677671501826 (by exact J2EntryWindow.get 2),
   DirectGuard.opAt 3686 .CALLDATASIZE (by exact J2EntryWindow.get 3),
   DirectGuard.opAt 3687 .SHR (by exact J2EntryWindow.get 4),
   DirectGuard.opAt 3688 .AND (by exact J2EntryWindow.get 5),
   DirectGuard.pushAt 3689 1 110 (by exact J2EntryWindow.get 6)]

private def maskJump : List Located :=
  [DirectGuard.opAt 3690 .JUMPI (by exact J2EntryWindow.get 7)]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 67 .JUMPDEST]

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_mask_entry (input : ByteArray) :
    DirectGuard.run maskEntry (PatternedScan.stS input 4827 []) =
      some (PatternedScan.stS input 4828 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3683 4827 [] (by norm_num) pc3836)
    (PatternedScan.stepS_jumpdest input 4827 [] (by simp) (by norm_num))

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 4828 []) =
      some (PatternedScan.stS input 4853 [110, sizeBit input]) := by
  have hpc : Artifact.submissionArtifact.instructionPC 3684 = 4828 := pc3837
  simp (config := {maxSteps := 400000}) [sizePrefix, sizeBit, DirectGuard.opAt,
    DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState, hpc,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat, RawExpressionAC.land_comm]

private theorem run_mask_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4853 [110, sizeBit input]) =
      some (PatternedScan.stS input 110 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3690 4853 [110, sizeBit input] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_taken input 4853 110 110 (sizeBit input) []
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_mask_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4853 [110, sizeBit input]) =
      some (PatternedScan.stS input 4854 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3690 4853 [110, sizeBit input] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_fall input 4853 110 (sizeBit input) []
      (by simp) (by norm_num) hc)

private theorem run_guard_match_tail (input : ByteArray) :
    DirectGuard.run guardMatchTail (PatternedScan.stS input 110 []) =
      some (PatternedScan.patternedEntry input) := by
  simp
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     PatternedScan.stS, PatternedScan.patternedEntry,
     Challenge.EvmProof.DataStepper.runLocatedBlock,
     Challenge.EvmProof.DataStepper.runLocated,
     Challenge.EvmProof.DataStepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

private def gasSteps_mask_prefix (input : ByteArray) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4853 [110, sizeBit input]) :=
  (sound maskEntry (run_mask_entry input)).trans (sound sizePrefix (run_size_prefix input))

private def gasSteps_mask_match (input : ByteArray) (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) := by
  have hf := sizeFlag_hit input hsize
  rw [← sizeBit_flag] at hf
  have hc : UInt256.isTrue (sizeBit input) := by
    change (sizeBit input).toNat ≠ 0
    intro hz
    rw [UInt256.isZero, if_pos hz] at hf
    exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) hf
  exact (gasSteps_mask_prefix input).trans
    ((sound maskJump (run_mask_match input hc)).trans (sound guardMatchTail (run_guard_match_tail input)))

private def gasSteps_mask_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4854 []) := by
  have hf := sizeFlag_fail input hfit hbad
  rw [← sizeBit_flag] at hf
  have hc : ¬ UInt256.isTrue (sizeBit input) := by
    intro ht
    change (sizeBit input).toNat ≠ 0 at ht
    rw [UInt256.isZero, if_neg ht] at hf
    exact (by decide : UInt256.ofNat 0 ≠ UInt256.ofNat 1) hf
  exact (gasSteps_mask_prefix input).trans (sound maskJump (run_mask_fall input hc))

/-! ## The 256 / 376 / 1000 test -/

private def lengthCond (input : ByteArray) : UInt256 :=
  UInt256.lor
    (UInt256.lor (UInt256.eq 1000 (UInt256.ofNat input.size)) (UInt256.eq 376 (UInt256.ofNat input.size)))
    (UInt256.eq 256 (UInt256.ofNat input.size))

private def lengthPrefix : List Located :=
  [DirectGuard.pushAt 3691 2 1016 (by exact J2EntryWindow.get 8),
   DirectGuard.pushAt 3692 5 6308489473 (by exact J2EntryWindow.get 9),
   DirectGuard.opAt 3693 .CALLDATASIZE (by exact J2EntryWindow.get 10),
   DirectGuard.pushAt 3694 1 24 (by exact J2EntryWindow.get 11),
   DirectGuard.opAt 3695 .AND (by exact J2EntryWindow.get 12),
   DirectGuard.opAt 3696 .SHR (by exact J2EntryWindow.get 13),
   DirectGuard.opAt 3697 .AND (by exact J2EntryWindow.get 14),
   DirectGuard.opAt 3698 .CALLDATASIZE (by exact J2EntryWindow.get 15),
   DirectGuard.opAt 3699 .EQ (by exact J2EntryWindow.get 16),
   DirectGuard.pushAt 3700 1 110 (by exact J2EntryWindow.get 17)]

private def lengthJump : List Located :=
  [DirectGuard.opAt 3701 .JUMPI (by exact J2EntryWindow.get 18)]

private theorem run_length_prefix (input : ByteArray) :
    DirectGuard.run lengthPrefix (PatternedScan.stS input 4854 []) =
      some (PatternedScan.stS input 4873 [110, lengthCond input]) := by
  have hf := PackedLengthLookup.flag (UInt256.ofNat input.size)
  change UInt256.eq (UInt256.ofNat input.size)
    (PackedLengthLookup.lookup (UInt256.ofNat input.size)) = lengthCond input at hf
  rw [← hf]
  have heq (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
    simp [UInt256.eq, eq_comm]
  simp (config := {maxSteps := 400000}) [lengthPrefix, PackedLengthLookup.lookup,
    DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS,
    initialState, DataStepper.runLocatedBlock, DataStepper.runLocated,
    DataStepper.runInstr, Word.literal_eq_ofNat, Word.succ_ofNat_mod,
    Word.ofNat_add_mod, Word.word_toNat_ofNat,
    packedPC3735, packedPC3736, packedPC3737, packedPC3738, packedPC3739,
    packedPC3740, packedPC3741, packedPC3742, packedPC3743, packedPC3744,
    heq, RawExpressionAC.land_comm]

private theorem lengthCond_true (input : ByteArray) (hsize : input.size = 256 ∨ input.size = 376 ∨ input.size = 1000) :
    UInt256.isTrue (lengthCond input) := by
  have hlt : input.size < 2 ^ 256 := by omega
  rcases hsize with h | h | h
  · rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376, Word.literal_eq_ofNat 1000,
      DirectGuard.size_eq_one input 256 h,
      DirectGuard.size_eq_zero input 376 hlt (by norm_num) (by omega),
      DirectGuard.size_eq_zero input 1000 hlt (by norm_num) (by omega)]
    decide
  · rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376, Word.literal_eq_ofNat 1000,
      DirectGuard.size_eq_zero input 256 hlt (by norm_num) (by omega),
      DirectGuard.size_eq_one input 376 h,
      DirectGuard.size_eq_zero input 1000 hlt (by norm_num) (by omega)]
    decide
  · rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376, Word.literal_eq_ofNat 1000,
      DirectGuard.size_eq_zero input 256 hlt (by norm_num) (by omega),
      DirectGuard.size_eq_zero input 376 hlt (by norm_num) (by omega),
      DirectGuard.size_eq_one input 1000 h]
    decide

private theorem lengthCond_false (input : ByteArray) (hfit : CalldataFits input)
    (h256 : input.size ≠ 256) (h376 : input.size ≠ 376) (h1000 : input.size ≠ 1000) :
    ¬ UInt256.isTrue (lengthCond input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376, Word.literal_eq_ofNat 1000,
    DirectGuard.size_eq_zero input 256 hlt (by norm_num) h256,
    DirectGuard.size_eq_zero input 376 hlt (by norm_num) h376,
    DirectGuard.size_eq_zero input 1000 hlt (by norm_num) h1000]
  decide

private def gasSteps_length_match (input : ByteArray)
    (hsize : input.size = 256 ∨ input.size = 376 ∨ input.size = 1000) :
    GasSteps (PatternedScan.stS input 4854 []) (PatternedScan.patternedEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4873 [110, lengthCond input]) =
      some (PatternedScan.stS input 110 []) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3701 4873 _ (by norm_num) packedPC3745)
      (PatternedScan.stepS_jumpi_taken input 4873 110 110 (lengthCond input) []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (lengthCond_true input hsize) guard_match_dest)
  exact (sound lengthPrefix (run_length_prefix input)).trans
    ((sound lengthJump hj).trans (sound guardMatchTail (run_guard_match_tail input)))

private def gasSteps_length_fail (input : ByteArray) (hfit : CalldataFits input)
    (h256 : input.size ≠ 256) (h376 : input.size ≠ 376) (h1000 : input.size ≠ 1000) :
    GasSteps (PatternedScan.stS input 4854 []) (AbcArm.armEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4873 [110, lengthCond input]) =
      some (AbcArm.armEntry input) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3701 4873 _ (by norm_num) packedPC3745)
      (PatternedScan.stepS_jumpi_fall input 4873 110 (lengthCond input) []
        (by simp) (by norm_num) (lengthCond_false input hfit h256 h376 h1000))
  exact (sound lengthPrefix (run_length_prefix input)).trans (sound lengthJump hj)

/-! ## Public routes -/

private theorem small_or_large (n : Nat) (h : RecognitionAccumulator.Allowed n) :
    (n = 56 ∨ n = 120 ∨ n = 63 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 119 ∨ n = 55 ∨ n = 1 ∨ n = 31 ∨ n = 32) ∨
      (n ≠ 56 ∧ n ≠ 120 ∧ n ≠ 63 ∧ n ≠ 64 ∧ n ≠ 65 ∧ n ≠ 128 ∧ n ≠ 119 ∧ n ≠ 55 ∧ n ≠ 1 ∧ n ≠ 31 ∧ n ≠ 32) ∧
        (n = 256 ∨ n = 376 ∨ n = 1000) := by
  unfold RecognitionAccumulator.Allowed at h
  omega

/-- An allowed length with first byte 7 reaches the scanner. -/
def gasSteps_allowed (input : ByteArray) (hfit : CalldataFits input)
    (hallowed : RecognitionAccumulator.Allowed input.size) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) := by
  by_cases hsmall : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32
  · exact gasSteps_mask_match input hsmall
  · have hcases := small_or_large input.size hallowed
    have hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by
      omega
    have hlarge : input.size = 256 ∨ input.size = 376 ∨ input.size = 1000 := by omega
    exact (gasSteps_mask_fail input hfit hbad).trans (gasSteps_length_match input hlarge)

/-- Any other length falls through into the tiny-input arm. -/
def gasSteps_to_arm (input : ByteArray) (hfit : CalldataFits input)
    (hdis : ¬ RecognitionAccumulator.Allowed input.size) :
    GasSteps (DirectGuard.guardEntry input) (AbcArm.armEntry input) := by
  unfold RecognitionAccumulator.Allowed at hdis
  have hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by
    omega
  exact (gasSteps_mask_fail input hfit hbad).trans
    (gasSteps_length_fail input hfit (by omega) (by omega) (by omega))

/-- With first byte 7, a length without a stored digest reaches the generic arm. -/
def gasSteps_disallowed (input : ByteArray) (hfit : CalldataFits input)
    (hbyte : DirectGuard.firstByte input = 7)
    (hdis : ¬ RecognitionAccumulator.Allowed input.size) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  (gasSteps_to_arm input hfit hdis).trans
    (AbcArm.gasSteps_miss input (EntryGateLogic.wordCond_ne_zero_of_byte7 input hfit hbyte))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
