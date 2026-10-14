import Challenge.Ripemd160.Submission.Proofs.Bytecode.TwoLengthFlagAddition
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

Entered at pc 439 when the first calldata byte is 7, or when a short or
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

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 3530 = 4796 := J2EntryWindow.pcB 2

@[simp] private theorem bigPC : Artifact.submissionArtifact.instructionPC 3528 = 4793 := J2EntryWindow.pcB 0

@[simp] private theorem bigPushPC : Artifact.submissionArtifact.instructionPC 3529 = 4794 := J2EntryWindow.pcB 1

private theorem isValidJumpDest_of_pc (idx pc : Nat)
    (hpc : Artifact.submissionArtifact.instructionPC idx = pc)
    (hget : Artifact.submissionArtifact.instructions[idx]? = some (.op .JUMPDEST)) :
    Decode.isValidJumpDest submissionBytecode pc = true := by
  subst hpc
  exact Artifact.submissionArtifact.isValidJumpDest_index idx hget

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 4796 = true :=
  isValidJumpDest_of_pc 3530 4796 entryPC61 (J2EntryWindow.getB 2)

private theorem guard_big_dest : Decode.isValidJumpDest submissionBytecode 4793 = true :=
  isValidJumpDest_of_pc 3528 4793 bigPC (J2EntryWindow.getB 0)

private theorem calldatasize_step (input : ByteArray) (pc : Nat) (stk : List UInt256)
    (hlen : stk.length < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .CALLDATASIZE) (PatternedScan.stS input pc stk) =
      some (PatternedScan.stS input (pc + 1) (UInt256.ofNat input.size :: stk)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.Ripemd160.initialState_calldata,
    Challenge.EvmProof.Word.succ_ofNat hpc]

/-! ## Program counters in the guard window -/

private theorem pc3836 : Artifact.submissionArtifact.instructionPC 3440 = 4601 := J2EntryWindow.pc 0
private theorem pc3837 : Artifact.submissionArtifact.instructionPC 3441 = 4602 := J2EntryWindow.pc 1
private theorem pc3843 : Artifact.submissionArtifact.instructionPC 3448 = 4629 := J2EntryWindow.pc 8
private theorem packedPC3736 : Artifact.submissionArtifact.instructionPC 3450 = 4633 := J2EntryWindow.pc 10
private theorem packedPC3737 : Artifact.submissionArtifact.instructionPC 3451 = 4634 := J2EntryWindow.pc 11
private theorem packedPC3738 : Artifact.submissionArtifact.instructionPC 3452 = 4637 := J2EntryWindow.pc 12
private theorem packedPC3739 : Artifact.submissionArtifact.instructionPC 3453 = 4638 := J2EntryWindow.pc 13
private theorem packedPC3740 : Artifact.submissionArtifact.instructionPC 3454 = 4639 := J2EntryWindow.pc 14
private theorem packedPC3743 : Artifact.submissionArtifact.instructionPC 3455 = 4640 := J2EntryWindow.pc 15
private theorem packedPC3745 : Artifact.submissionArtifact.instructionPC 3456 = 4643 := J2EntryWindow.pc 16
private theorem packedPC3735 : Artifact.submissionArtifact.instructionPC 3449 = 4630 := J2EntryWindow.pc 9

@[simp] private theorem sizeHitPC3837 : Artifact.submissionArtifact.instructionPC 3442 = 4603 :=
  J2EntryWindow.pc 2
@[simp] private theorem sizeHitPC3838 : Artifact.submissionArtifact.instructionPC 3443 = 4605 :=
  J2EntryWindow.pc 3
@[simp] private theorem sizeHitPC3839 : Artifact.submissionArtifact.instructionPC 3444 = 4623 :=
  J2EntryWindow.pc 4
@[simp] private theorem sizeHitPC3840 : Artifact.submissionArtifact.instructionPC 3445 = 4624 :=
  J2EntryWindow.pc 5
@[simp] private theorem sizeHitPC3841 : Artifact.submissionArtifact.instructionPC 3446 = 4625 :=
  J2EntryWindow.pc 6
@[simp] private theorem sizeHitPC3842 : Artifact.submissionArtifact.instructionPC 3447 = 4626 :=
  J2EntryWindow.pc 7

/-! ## The size mask -/

private def maskEntry : List Located :=
  [DirectGuard.opAt 3440 .JUMPDEST (by exact J2EntryWindow.get 0)]

private def sizePrefix : List Located :=
  [DirectGuard.opAt 3441 .CALLDATASIZE (by exact J2EntryWindow.get 1),
   DirectGuard.pushAt 3442 1 1 (by exact J2EntryWindow.get 2),
   DirectGuard.pushAt 3443 17 342276208914615837337402008677671501826 (by exact J2EntryWindow.get 3),
   DirectGuard.opAt 3444 .CALLDATASIZE (by exact J2EntryWindow.get 4),
   DirectGuard.opAt 3445 .SHR (by exact J2EntryWindow.get 5),
   DirectGuard.opAt 3446 .AND (by exact J2EntryWindow.get 6),
   DirectGuard.pushAt 3447 2 4796 (by exact J2EntryWindow.get 7)]

private def maskJump : List Located :=
  [DirectGuard.opAt 3448 .JUMPI (by exact J2EntryWindow.get 8)]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 3530 .JUMPDEST (by exact J2EntryWindow.getB 2)]

/-- The 256/376/1000 entry: `JUMPDEST PUSH1 251`, falling into the shared scanner entry. -/
private def bigTail : List Located :=
  [DirectGuard.opAt 3528 .JUMPDEST (by exact J2EntryWindow.getB 0),
   DirectGuard.pushAt 3529 1 251 (by exact J2EntryWindow.getB 1)]

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_mask_entry (input : ByteArray) :
    DirectGuard.run maskEntry (PatternedScan.stS input 4601 []) =
      some (PatternedScan.stS input 4602 []) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3440 4601 [] (by norm_num) pc3836)
    (PatternedScan.stepS_jumpdest input 4601 [] (by simp) (by norm_num))

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 4602 []) =
      some (PatternedScan.stS input 4629 [4796, sizeBit input, UInt256.ofNat input.size]) := by
  have hpc : Artifact.submissionArtifact.instructionPC 3441 = 4602 := pc3837
  simp (config := {maxSteps := 400000}) [sizePrefix, sizeBit, DirectGuard.opAt,
    DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState, hpc,
    DataStepper.runLocatedBlock, DataStepper.runLocated, DataStepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat, RawExpressionAC.land_comm]

private theorem run_mask_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4629 [4796, sizeBit input, UInt256.ofNat input.size]) =
      some (PatternedScan.stS input 4796 [UInt256.ofNat input.size]) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3448 4629 [4796, sizeBit input, UInt256.ofNat input.size] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_taken input 4629 4796 4796 (sizeBit input) [UInt256.ofNat input.size]
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_mask_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run maskJump (PatternedScan.stS input 4629 [4796, sizeBit input, UInt256.ofNat input.size]) =
      some (PatternedScan.stS input 4630 [UInt256.ofNat input.size]) :=
  PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 3448 4629 [4796, sizeBit input, UInt256.ofNat input.size] (by norm_num) pc3843)
    (PatternedScan.stepS_jumpi_fall input 4629 4796 (sizeBit input) [UInt256.ofNat input.size]
      (by simp) (by norm_num) hc)

private theorem run_guard_match_tail (input : ByteArray) (v : UInt256)
    (hv : v = PatternedScan.segEnd input.size) :
    DirectGuard.run guardMatchTail (PatternedScan.stS input 4796 [v]) =
      some (PatternedScan.patternedEntry input) := by
  subst hv
  simp
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     PatternedScan.stS, PatternedScan.patternedEntry,
     Challenge.EvmProof.DataStepper.runLocatedBlock,
     Challenge.EvmProof.DataStepper.runLocated,
     Challenge.EvmProof.DataStepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

private theorem run_big_tail (input : ByteArray) :
    DirectGuard.run bigTail (PatternedScan.stS input 4793 []) =
      some (PatternedScan.stS input 4796 [UInt256.ofNat 251]) := by
  simp
    [bigTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     PatternedScan.stS,
     Challenge.EvmProof.DataStepper.runLocatedBlock,
     Challenge.EvmProof.DataStepper.runLocated,
     Challenge.EvmProof.DataStepper.runInstr,
     Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

private theorem segEnd_small (n : Nat) (hsize : n = 56 ∨ n = 120 ∨ n = 63 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 119 ∨ n = 55 ∨ n = 1 ∨ n = 31 ∨ n = 32) :
    UInt256.ofNat n = PatternedScan.segEnd n := by
  rcases hsize with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

private theorem segEnd_large (n : Nat) (hsize : n = 256 ∨ n = 376 ∨ n = 1000) :
    UInt256.ofNat 251 = PatternedScan.segEnd n := by
  rcases hsize with h | h | h <;> subst h <;> decide

private def gasSteps_mask_prefix (input : ByteArray) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4629 [4796, sizeBit input, UInt256.ofNat input.size]) :=
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
    ((sound maskJump (run_mask_match input hc)).trans
      (sound guardMatchTail (run_guard_match_tail input _ (segEnd_small input.size hsize))))

private def gasSteps_mask_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4630 [UInt256.ofNat input.size]) := by
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
  UInt256.lor (UInt256.eq 376 (UInt256.ofNat input.size))
    (UInt256.eq 256 (UInt256.ofNat input.size))

private def lengthPrefix : List Located :=
  [DirectGuard.pushAt 3449 2 256 (by exact J2EntryWindow.get 9),
   DirectGuard.opAt 3450 .EQ (by exact J2EntryWindow.get 10),
   DirectGuard.pushAt 3451 2 376 (by exact J2EntryWindow.get 11),
   DirectGuard.opAt 3452 .CALLDATASIZE (by exact J2EntryWindow.get 12),
   DirectGuard.opAt 3453 .EQ (by exact J2EntryWindow.get 13),
   DirectGuard.opAt 3454 .ADD (by exact J2EntryWindow.get 14),
   DirectGuard.pushAt 3455 2 4793 (by exact J2EntryWindow.get 15)]

private def lengthJump : List Located :=
  [DirectGuard.opAt 3456 .JUMPI (by exact J2EntryWindow.get 16)]

private theorem run_length_prefix (input : ByteArray) :
    DirectGuard.run lengthPrefix (PatternedScan.stS input 4630 [UInt256.ofNat input.size]) =
      some (PatternedScan.stS input 4643 [4793, lengthCond input]) := by
  have heq (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
    simp [UInt256.eq, eq_comm]
  simp (config := {maxSteps := 400000}) [lengthPrefix, lengthCond,
    DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS,
    initialState, DataStepper.runLocatedBlock, DataStepper.runLocated,
    DataStepper.runInstr, Word.literal_eq_ofNat, Word.succ_ofNat_mod,
    Word.ofNat_add_mod, Word.word_toNat_ofNat,
    packedPC3735, packedPC3736, packedPC3737, packedPC3738, packedPC3739,
    packedPC3740, packedPC3743, heq, RawExpressionAC.lor_comm]

  have hadd (a b : UInt256) : UInt256.add a b = a + b := rfl
  simpa only [heq, hadd, RawExpressionAC.lor_comm] using
    TwoLengthFlagAddition.add_flags_eq_or (UInt256.ofNat input.size)

private theorem lengthCond_true (input : ByteArray) (hsize : input.size = 256 ∨ input.size = 376) :
    UInt256.isTrue (lengthCond input) := by
  have hlt : input.size < 2 ^ 256 := by omega
  rcases hsize with h | h
  · rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376,
      DirectGuard.size_eq_one input 256 h,
      DirectGuard.size_eq_zero input 376 hlt (by norm_num) (by omega)]
    decide
  · rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376,
      DirectGuard.size_eq_zero input 256 hlt (by norm_num) (by omega),
      DirectGuard.size_eq_one input 376 h]
    decide

private theorem lengthCond_false (input : ByteArray) (hfit : CalldataFits input)
    (h256 : input.size ≠ 256) (h376 : input.size ≠ 376) :
    ¬ UInt256.isTrue (lengthCond input) := by
  have hlt : input.size < 2 ^ 256 := Nat.lt_trans hfit (by norm_num)
  rw [lengthCond, Word.literal_eq_ofNat 256, Word.literal_eq_ofNat 376,
    DirectGuard.size_eq_zero input 256 hlt (by norm_num) h256,
    DirectGuard.size_eq_zero input 376 hlt (by norm_num) h376]
  decide

private def gasSteps_length_match (input : ByteArray)
    (hsize : input.size = 256 ∨ input.size = 376) :
    GasSteps (PatternedScan.stS input 4630 [UInt256.ofNat input.size]) (PatternedScan.patternedEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4643 [4793, lengthCond input]) =
      some (PatternedScan.stS input 4793 []) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3456 4643 _ (by norm_num) packedPC3745)
      (PatternedScan.stepS_jumpi_taken input 4643 4793 4793 (lengthCond input) []
        (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _)
        (lengthCond_true input hsize) guard_big_dest)
  exact (sound lengthPrefix (run_length_prefix input)).trans
    ((sound lengthJump hj).trans ((sound bigTail (run_big_tail input)).trans
      (sound guardMatchTail (run_guard_match_tail input _
        (segEnd_large input.size (hsize.elim Or.inl (fun h => Or.inr (Or.inl h))))))))

private def gasSteps_length_fail (input : ByteArray) (hfit : CalldataFits input)
    (h256 : input.size ≠ 256) (h376 : input.size ≠ 376) :
    GasSteps (PatternedScan.stS input 4630 [UInt256.ofNat input.size]) (AbcArm.armEntry input) := by
  have hj : DirectGuard.run lengthJump (PatternedScan.stS input 4643 [4793, lengthCond input]) =
      some (AbcArm.armEntry input) :=
    PatternedScan.blockOfS _
      (PatternedScan.pcFactS input 3456 4643 _ (by norm_num) packedPC3745)
      (PatternedScan.stepS_jumpi_fall input 4643 4793 (lengthCond input) []
        (by simp) (by norm_num) (lengthCond_false input hfit h256 h376))
  exact (sound lengthPrefix (run_length_prefix input)).trans (sound lengthJump hj)

/-! ## Public routes -/

/-- The long-length entry at 4793 reaches the scanner with the segment end 251 pushed. -/
def gasSteps_big_entry (input : ByteArray) (hsize : input.size = 256 ∨ input.size = 376 ∨ input.size = 1000) :
    GasSteps (PatternedScan.stS input 4793 []) (PatternedScan.patternedEntry input) :=
  (sound bigTail (run_big_tail input)).trans
    (sound guardMatchTail (run_guard_match_tail input _ (segEnd_large input.size hsize)))

private theorem small_or_large (n : Nat) (h : RecognitionAccumulator.Allowed n) :
    (n = 56 ∨ n = 120 ∨ n = 63 ∨ n = 64 ∨ n = 65 ∨ n = 128 ∨ n = 119 ∨ n = 55 ∨ n = 1 ∨ n = 31 ∨ n = 32) ∨
      (n ≠ 56 ∧ n ≠ 120 ∧ n ≠ 63 ∧ n ≠ 64 ∧ n ≠ 65 ∧ n ≠ 128 ∧ n ≠ 119 ∧ n ≠ 55 ∧ n ≠ 1 ∧ n ≠ 31 ∧ n ≠ 32) ∧
        (n = 256 ∨ n = 376 ∨ n = 1000) := by
  unfold RecognitionAccumulator.Allowed at h
  omega

/-- An allowed length with first byte 7 reaches the scanner. -/
def gasSteps_allowed (input : ByteArray) (hfit : CalldataFits input)
    (hallowed : RecognitionAccumulator.Allowed input.size) (h1000 : input.size ≠ 1000) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) := by
  by_cases hsmall : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32
  · exact gasSteps_mask_match input hsmall
  · have hcases := small_or_large input.size hallowed
    have hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by
      omega
    have hlarge : input.size = 256 ∨ input.size = 376 := by omega
    exact (gasSteps_mask_fail input hfit hbad).trans (gasSteps_length_match input hlarge)

/-- Any other length falls through into the tiny-input arm. -/
def gasSteps_to_arm (input : ByteArray) (hfit : CalldataFits input)
    (hdis : ¬ RecognitionAccumulator.Allowed input.size) (_h1000 : input.size ≠ 1000) :
    GasSteps (DirectGuard.guardEntry input) (AbcArm.armEntry input) := by
  unfold RecognitionAccumulator.Allowed at hdis
  have hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by
    omega
  exact (gasSteps_mask_fail input hfit hbad).trans
    (gasSteps_length_fail input hfit (by omega) (by omega))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
