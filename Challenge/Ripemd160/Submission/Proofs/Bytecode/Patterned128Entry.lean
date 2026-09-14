import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLengthLookup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GuardInstructionWindow
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

Entered at pc 4803 when the first calldata byte is 7, or when a short or
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

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 68 = 110 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 110 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 68 (by rfl)

private theorem calldatasize_step (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

/-! ## Program counters in the guard window -/

private theorem pc3836 : Artifact.submissionArtifact.instructionPC 3749 = 4840 := GuardInstructionWindow.pc 194
private theorem pc3837 : Artifact.submissionArtifact.instructionPC 3750 = 4841 := GuardInstructionWindow.pc 195
private theorem pc3843 : Artifact.submissionArtifact.instructionPC 3756 = 4866 := GuardInstructionWindow.pc 201
private theorem pc3844 : Artifact.submissionArtifact.instructionPC 3757 = 4867 := GuardInstructionWindow.pc 202
private theorem packedPC3748 : Artifact.submissionArtifact.instructionPC 3757 = 4867 := GuardInstructionWindow.pc 202
private theorem packedPC3749 : Artifact.submissionArtifact.instructionPC 3758 = 4873 := GuardInstructionWindow.pc 203
private theorem packedPC3750 : Artifact.submissionArtifact.instructionPC 3759 = 4874 := GuardInstructionWindow.pc 204
private theorem packedPC3751 : Artifact.submissionArtifact.instructionPC 3760 = 4876 := GuardInstructionWindow.pc 205
private theorem packedPC3752 : Artifact.submissionArtifact.instructionPC 3761 = 4877 := GuardInstructionWindow.pc 206
private theorem packedPC3753 : Artifact.submissionArtifact.instructionPC 3762 = 4878 := GuardInstructionWindow.pc 207
private theorem packedPC3754 : Artifact.submissionArtifact.instructionPC 3763 = 4881 := GuardInstructionWindow.pc 208
private theorem packedPC3755 : Artifact.submissionArtifact.instructionPC 3764 = 4882 := GuardInstructionWindow.pc 209
private theorem packedPC3756 : Artifact.submissionArtifact.instructionPC 3765 = 4883 := GuardInstructionWindow.pc 210
private theorem packedPC3757 : Artifact.submissionArtifact.instructionPC 3766 = 4884 := GuardInstructionWindow.pc 211
private theorem packedPC3758 : Artifact.submissionArtifact.instructionPC 3767 = 4886 := GuardInstructionWindow.pc 212

@[simp] private theorem sizeHitPC3838 : Artifact.submissionArtifact.instructionPC 3751 = 4843 :=
  GuardInstructionWindow.pc 196
@[simp] private theorem sizeHitPC3839 : Artifact.submissionArtifact.instructionPC 3752 = 4861 :=
  GuardInstructionWindow.pc 197
@[simp] private theorem sizeHitPC3840 : Artifact.submissionArtifact.instructionPC 3753 = 4862 :=
  GuardInstructionWindow.pc 198
@[simp] private theorem sizeHitPC3841 : Artifact.submissionArtifact.instructionPC 3754 = 4863 :=
  GuardInstructionWindow.pc 199
@[simp] private theorem sizeHitPC3842 : Artifact.submissionArtifact.instructionPC 3755 = 4864 :=
  GuardInstructionWindow.pc 200

/-! ## The size mask -/

private def maskEntry : List Located :=
  [DirectGuard.opAt 3749 .JUMPDEST (by exact GuardInstructionWindow.get 194)]

private def sizePrefix : List Located :=
  [DirectGuard.pushAt 3750 1 1 (by exact GuardInstructionWindow.get 195),
   DirectGuard.pushAt 3751 17 342276208914615837337402008677671501826 (by exact GuardInstructionWindow.get 196),
   DirectGuard.opAt 3752 .CALLDATASIZE (by exact GuardInstructionWindow.get 197),
   DirectGuard.opAt 3753 .SHR (by exact GuardInstructionWindow.get 198),
   DirectGuard.opAt 3754 .AND (by exact GuardInstructionWindow.get 199),
   DirectGuard.pushAt 3755 1 110 (by exact GuardInstructionWindow.get 200)]

private def maskJump : List Located :=
  [DirectGuard.opAt 3756 .JUMPI (by exact GuardInstructionWindow.get 201)]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 68 .JUMPDEST]

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_mask_entry (input : ByteArray) :
    DirectGuard.run maskEntry (PatternedScan.stS input 4840 []) =
      some (PatternedScan.stS input 4841 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3749 4840 [] (by norm_num) pc3836)
    (PatternedScan.stepS_jumpdest input 4840 [] (by simp) (by norm_num))

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 4841 []) =
      some (PatternedScan.stS input 4866 [110, sizeBit input]) := by
  have hpc : Artifact.submissionArtifact.instructionPC 3750 = 4841 := pc3837
  simp (config := {maxSteps := 400000}) [sizePrefix, sizeBit, DirectGuard.opAt,
    DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState, hpc,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat, RawExpressionAC.land_comm]

private theorem run_mask_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4866 [110, sizeBit input]) =
      some (PatternedScan.stS input 110 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3756 4866 [110, sizeBit input] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_taken input 4866 110 110 (sizeBit input) []
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_mask_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4866 [110, sizeBit input]) =
      some (PatternedScan.stS input 4867 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3756 4866 [110, sizeBit input] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_fall input 4866 110 (sizeBit input) []
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
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4866 [110, sizeBit input]) :=
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
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4867 []) := by
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
  [DirectGuard.pushAt 3757 5 6308489473 (by exact GuardInstructionWindow.get 202),
   DirectGuard.opAt 3758 .CALLDATASIZE (by exact GuardInstructionWindow.get 203),
   DirectGuard.pushAt 3759 1 24 (by exact GuardInstructionWindow.get 204),
   DirectGuard.opAt 3760 .AND (by exact GuardInstructionWindow.get 205),
   DirectGuard.opAt 3761 .SHR (by exact GuardInstructionWindow.get 206),
   DirectGuard.pushAt 3762 2 1016 (by exact GuardInstructionWindow.get 207),
   DirectGuard.opAt 3763 .AND (by exact GuardInstructionWindow.get 208),
   DirectGuard.opAt 3764 .CALLDATASIZE (by exact GuardInstructionWindow.get 209),
   DirectGuard.opAt 3765 .EQ (by exact GuardInstructionWindow.get 210),
   DirectGuard.pushAt 3766 1 110 (by exact GuardInstructionWindow.get 211)]

private def lengthJump : List Located :=
  [DirectGuard.opAt 3767 .JUMPI (by exact GuardInstructionWindow.get 212)]

private theorem run_length_prefix (input : ByteArray) :
    DirectGuard.run lengthPrefix (PatternedScan.stS input 4867 []) =
      some (PatternedScan.stS input 4886 [110, lengthCond input]) := by
  have hf := PackedLengthLookup.flag (UInt256.ofNat input.size)
  change UInt256.eq (UInt256.ofNat input.size)
    (PackedLengthLookup.lookup (UInt256.ofNat input.size)) = lengthCond input at hf
  rw [← hf]
  simp (config := {maxSteps := 400000}) [lengthPrefix, PackedLengthLookup.lookup,
    DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS,
    initialState, DataStepper.runLocatedBlock, DataStepper.runLocated,
    DataStepper.runInstr, Word.literal_eq_ofNat, Word.succ_ofNat_mod,
    Word.ofNat_add_mod, Word.word_toNat_ofNat,
    packedPC3748, packedPC3749, packedPC3750, packedPC3751, packedPC3752,
    packedPC3753, packedPC3754, packedPC3755, packedPC3756, packedPC3757]

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
    GasSteps (PatternedScan.stS input 4867 []) (PatternedScan.patternedEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4886 [110, lengthCond input]) =
      some (PatternedScan.stS input 110 []) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3767 4886 _ (by norm_num) packedPC3758)
      (PatternedScan.stepS_jumpi_taken input 4886 110 110 (lengthCond input) []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (lengthCond_true input hsize) guard_match_dest)
  exact (sound lengthPrefix (run_length_prefix input)).trans
    ((sound lengthJump hj).trans (sound guardMatchTail (run_guard_match_tail input)))

private def gasSteps_length_fail (input : ByteArray) (hfit : CalldataFits input)
    (h256 : input.size ≠ 256) (h376 : input.size ≠ 376) (h1000 : input.size ≠ 1000) :
    GasSteps (PatternedScan.stS input 4867 []) (AbcArm.armEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4886 [110, lengthCond input]) =
      some (AbcArm.armEntry input) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3767 4886 _ (by norm_num) packedPC3758)
      (PatternedScan.stepS_jumpi_fall input 4886 110 (lengthCond input) []
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
