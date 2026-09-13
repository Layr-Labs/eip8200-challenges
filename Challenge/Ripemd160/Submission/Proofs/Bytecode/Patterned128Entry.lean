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

Entered at pc 4805 when the first calldata byte is 7, or when a short or
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

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 71 = 115 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 115 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 71 (by rfl)

private theorem calldatasize_step (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

/-! ## Program counters in the guard window -/

private theorem pc3836 : Artifact.submissionArtifact.instructionPC 3795 = 4808 := GuardInstructionWindow.pc 185
private theorem pc3837 : Artifact.submissionArtifact.instructionPC 3796 = 4809 := GuardInstructionWindow.pc 186
private theorem pc3843 : Artifact.submissionArtifact.instructionPC 3802 = 4834 := GuardInstructionWindow.pc 192
private theorem pc3844 : Artifact.submissionArtifact.instructionPC 3803 = 4835 := GuardInstructionWindow.pc 193
private theorem pc3845 : Artifact.submissionArtifact.instructionPC 3804 = 4836 := GuardInstructionWindow.pc 194
private theorem pc3846 : Artifact.submissionArtifact.instructionPC 3805 = 4839 := GuardInstructionWindow.pc 195
private theorem pc3847 : Artifact.submissionArtifact.instructionPC 3806 = 4840 := GuardInstructionWindow.pc 196
private theorem pc3848 : Artifact.submissionArtifact.instructionPC 3807 = 4841 := GuardInstructionWindow.pc 197
private theorem pc3849 : Artifact.submissionArtifact.instructionPC 3808 = 4844 := GuardInstructionWindow.pc 198
private theorem pc3850 : Artifact.submissionArtifact.instructionPC 3809 = 4845 := GuardInstructionWindow.pc 199
private theorem pc3851 : Artifact.submissionArtifact.instructionPC 3810 = 4846 := GuardInstructionWindow.pc 200
private theorem pc3852 : Artifact.submissionArtifact.instructionPC 3811 = 4849 := GuardInstructionWindow.pc 201
private theorem pc3853 : Artifact.submissionArtifact.instructionPC 3812 = 4850 := GuardInstructionWindow.pc 202
private theorem pc3854 : Artifact.submissionArtifact.instructionPC 3813 = 4851 := GuardInstructionWindow.pc 203
private theorem pc3855 : Artifact.submissionArtifact.instructionPC 3814 = 4852 := GuardInstructionWindow.pc 204
private theorem pc3856 : Artifact.submissionArtifact.instructionPC 3815 = 4854 := GuardInstructionWindow.pc 205

@[simp] private theorem sizeHitPC3838 : Artifact.submissionArtifact.instructionPC 3797 = 4827 :=
  GuardInstructionWindow.pc 187
@[simp] private theorem sizeHitPC3839 : Artifact.submissionArtifact.instructionPC 3798 = 4828 :=
  GuardInstructionWindow.pc 188
@[simp] private theorem sizeHitPC3840 : Artifact.submissionArtifact.instructionPC 3799 = 4829 :=
  GuardInstructionWindow.pc 189
@[simp] private theorem sizeHitPC3841 : Artifact.submissionArtifact.instructionPC 3800 = 4831 :=
  GuardInstructionWindow.pc 190
@[simp] private theorem sizeHitPC3842 : Artifact.submissionArtifact.instructionPC 3801 = 4832 :=
  GuardInstructionWindow.pc 191

/-! ## The size mask -/

private def maskEntry : List Located :=
  [DirectGuard.opAt 3795 .JUMPDEST (by exact GuardInstructionWindow.get 185)]

private def sizePrefix : List Located :=
  [DirectGuard.pushAt 3796 17 342276208914615837337402008677671501826 (by exact GuardInstructionWindow.get 186),
   DirectGuard.opAt 3797 .CALLDATASIZE (by exact GuardInstructionWindow.get 187),
   DirectGuard.opAt 3798 .SHR (by exact GuardInstructionWindow.get 188),
   DirectGuard.pushAt 3799 1 1 (by exact GuardInstructionWindow.get 189),
   DirectGuard.opAt 3800 .AND (by exact GuardInstructionWindow.get 190),
   DirectGuard.pushAt 3801 1 115 (by exact GuardInstructionWindow.get 191)]

private def maskJump : List Located :=
  [DirectGuard.opAt 3802 .JUMPI (by exact GuardInstructionWindow.get 192)]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 71 .JUMPDEST]

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_mask_entry (input : ByteArray) :
    DirectGuard.run maskEntry (PatternedScan.stS input 4808 []) =
      some (PatternedScan.stS input 4809 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3795 4808 [] (by norm_num) pc3836)
    (PatternedScan.stepS_jumpdest input 4808 [] (by simp) (by norm_num))

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 4809 []) =
      some (PatternedScan.stS input 4834 [115, sizeBit input]) := by
  have hpc : Artifact.submissionArtifact.instructionPC 3796 = 4809 := pc3837
  simp (config := {maxSteps := 400000}) [sizePrefix, sizeBit, DirectGuard.opAt,
    DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState, hpc,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

private theorem run_mask_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4834 [115, sizeBit input]) =
      some (PatternedScan.stS input 115 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3802 4834 [115, sizeBit input] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_taken input 4834 115 115 (sizeBit input) []
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_mask_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4834 [115, sizeBit input]) =
      some (PatternedScan.stS input 4835 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3802 4834 [115, sizeBit input] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_fall input 4834 115 (sizeBit input) []
      (by simp) (by norm_num) hc)

private theorem run_guard_match_tail (input : ByteArray) :
    DirectGuard.run guardMatchTail (PatternedScan.stS input 115 []) =
      some (PatternedScan.patternedEntry input) := by
  simp
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     PatternedScan.stS, PatternedScan.patternedEntry,
     Challenge.EvmProof.DataStepper.runLocatedBlock,
     Challenge.EvmProof.DataStepper.runLocated,
     Challenge.EvmProof.DataStepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

private def gasSteps_mask_prefix (input : ByteArray) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4834 [115, sizeBit input]) :=
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
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4835 []) := by
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
  [DirectGuard.opAt 3803 .CALLDATASIZE (by exact GuardInstructionWindow.get 193),
   DirectGuard.pushAt 3804 2 256 (by exact GuardInstructionWindow.get 194),
   DirectGuard.opAt 3805 .EQ (by exact GuardInstructionWindow.get 195),
   DirectGuard.opAt 3806 .CALLDATASIZE (by exact GuardInstructionWindow.get 196),
   DirectGuard.pushAt 3807 2 376 (by exact GuardInstructionWindow.get 197),
   DirectGuard.opAt 3808 .EQ (by exact GuardInstructionWindow.get 198),
   DirectGuard.opAt 3809 .CALLDATASIZE (by exact GuardInstructionWindow.get 199),
   DirectGuard.pushAt 3810 2 1000 (by exact GuardInstructionWindow.get 200),
   DirectGuard.opAt 3811 .EQ (by exact GuardInstructionWindow.get 201),
   DirectGuard.opAt 3812 .OR (by exact GuardInstructionWindow.get 202),
   DirectGuard.opAt 3813 .OR (by exact GuardInstructionWindow.get 203),
   DirectGuard.pushAt 3814 1 115 (by exact GuardInstructionWindow.get 204)]

private def lengthJump : List Located :=
  [DirectGuard.opAt 3815 .JUMPI (by exact GuardInstructionWindow.get 205)]

private theorem run_length_prefix (input : ByteArray) :
    DirectGuard.run lengthPrefix (PatternedScan.stS input 4835 []) =
      some (PatternedScan.stS input 4854 [115, lengthCond input]) := by
  let n := UInt256.ofNat input.size
  let e256 := UInt256.eq 256 n
  let e376 := UInt256.eq 376 n
  let e1000 := UInt256.eq 1000 n
  let l0 : Located := DirectGuard.opAt 3803 .CALLDATASIZE (by exact GuardInstructionWindow.get 193)
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 3803 4835 [] (by norm_num) pc3844)
    (calldatasize_step input 4835 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 3804 2 256 (by exact GuardInstructionWindow.get 194)
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 3804 4836 [n] (by norm_num) pc3845)
    (PatternedScan.stepS_push input 4836 2 256 [n] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 3805 .EQ (by exact GuardInstructionWindow.get 195)
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 3805 4839 [256, n] (by norm_num) pc3846)
    (PatternedScan.stepS_eq input 4839 256 n [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.opAt 3806 .CALLDATASIZE (by exact GuardInstructionWindow.get 196)
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 3806 4840 [e256] (by norm_num) pc3847)
    (calldatasize_step input 4840 [e256] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.pushAt 3807 2 376 (by exact GuardInstructionWindow.get 197)
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 3807 4841 [n, e256] (by norm_num) pc3848)
    (PatternedScan.stepS_push input 4841 2 376 [n, e256] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := DirectGuard.opAt 3808 .EQ (by exact GuardInstructionWindow.get 198)
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 3808 4844 [376, n, e256] (by norm_num) pc3849)
    (PatternedScan.stepS_eq input 4844 376 n [e256] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.opAt 3809 .CALLDATASIZE (by exact GuardInstructionWindow.get 199)
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 3809 4845 [e376, e256] (by norm_num) pc3850)
    (calldatasize_step input 4845 [e376, e256] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 3810 2 1000 (by exact GuardInstructionWindow.get 200)
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 3810 4846 [n, e376, e256] (by norm_num) pc3851)
    (PatternedScan.stepS_push input 4846 2 1000 [n, e376, e256] (by simp) (by decide) (by decide) (by norm_num))
  let l8 : Located := DirectGuard.opAt 3811 .EQ (by exact GuardInstructionWindow.get 201)
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 3811 4849 [1000, n, e376, e256] (by norm_num) pc3852)
    (PatternedScan.stepS_eq input 4849 1000 n [e376, e256] (by simp) (by norm_num))
  let l9 : Located := DirectGuard.opAt 3812 .OR (by exact GuardInstructionWindow.get 202)
  have h9 := PatternedScan.blockOfS l9
    (PatternedScan.pcFactS input 3812 4850 [e1000, e376, e256] (by norm_num) pc3853)
    (PatternedScan.stepS_or input 4850 e1000 e376 [e256] (by simp) (by norm_num))
  let l10 : Located := DirectGuard.opAt 3813 .OR (by exact GuardInstructionWindow.get 203)
  have h10 := PatternedScan.blockOfS l10
    (PatternedScan.pcFactS input 3813 4851 [UInt256.lor e1000 e376, e256] (by norm_num) pc3854)
    (PatternedScan.stepS_or input 4851 (UInt256.lor e1000 e376) e256 [] (by simp) (by norm_num))
  let l11 : Located := DirectGuard.pushAt 3814 1 115 (by exact GuardInstructionWindow.get 204)
  have h11 := PatternedScan.blockOfS l11
    (PatternedScan.pcFactS input 3814 4852 [UInt256.lor (UInt256.lor e1000 e376) e256] (by norm_num) pc3855)
    (PatternedScan.stepS_push input 4852 1 115 [UInt256.lor (UInt256.lor e1000 e376) e256]
      (by simp) (by decide) (by decide) (by norm_num))
  have s1 := DataStepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have s2 := DataStepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ s1 rfl h2
  have s3 := DataStepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ s2 rfl h3
  have s4 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ s3 rfl h4
  have s5 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ s4 rfl h5
  have s6 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ s5 rfl h6
  have s7 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ s6 rfl h7
  have s8 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6, l7] [l8] _ _ _ s7 rfl h8
  have s9 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6, l7, l8] [l9] _ _ _ s8 rfl h9
  have s10 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9] [l10] _ _ _ s9 rfl h10
  have s11 := DataStepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10] [l11] _ _ _ s10 rfl h11
  exact s11

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
    GasSteps (PatternedScan.stS input 4835 []) (PatternedScan.patternedEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4854 [115, lengthCond input]) =
      some (PatternedScan.stS input 115 []) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3815 4854 _ (by norm_num) pc3856)
      (PatternedScan.stepS_jumpi_taken input 4854 115 115 (lengthCond input) []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (lengthCond_true input hsize) guard_match_dest)
  exact (sound lengthPrefix (run_length_prefix input)).trans
    ((sound lengthJump hj).trans (sound guardMatchTail (run_guard_match_tail input)))

private def gasSteps_length_fail (input : ByteArray) (hfit : CalldataFits input)
    (h256 : input.size ≠ 256) (h376 : input.size ≠ 376) (h1000 : input.size ≠ 1000) :
    GasSteps (PatternedScan.stS input 4835 []) (AbcArm.armEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4854 [115, lengthCond input]) =
      some (AbcArm.armEntry input) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3815 4854 _ (by norm_num) pc3856)
      (PatternedScan.stepS_jumpi_fall input 4854 115 (lengthCond input) []
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
