import Challenge.Ripemd160.Submission.Proofs.Bytecode.GuardInstructionWindow
import Challenge.Ripemd160.Submission.Proofs.Bytecode.AbcArm
import Challenge.Ripemd160.Submission.Proofs.Bytecode.SizeLookupFlag
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The appended 56/120/63-byte guard and its bridge into the patterned scan. -/

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
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 64 = 106 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 65 = 107 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

private theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (DirectGuard.firstByte input) := by
  simpa [DirectGuard.firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

private theorem guard_byte_eq_zero (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    UInt256.eq (UInt256.ofNat 7)
        (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)) =
      UInt256.ofNat 0 := by
  rw [firstByte_eq_byteAt]
  unfold UInt256.eq
  have hlt : DirectGuard.firstByte input < 2 ^ 256 := by
    unfold DirectGuard.firstByte
    exact Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt
      (by norm_num)
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt]
  simp [Ne.symm hbyte]

private def byteValue (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 7)
    (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0))

private theorem byteValue_zero (input : ByteArray) (hbyte : DirectGuard.firstByte input = 7) :
    byteValue input = UInt256.ofNat 0 := by
  rw [byteValue, firstByte_eq_byteAt, hbyte]
  decide

private theorem byteValue_true (input : ByteArray) (hbyte : DirectGuard.firstByte input ≠ 7) :
    UInt256.isTrue (byteValue input) := by
  intro hz
  have hx : UInt256.xor (UInt256.ofNat 7)
      (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)) = 0 :=
    Word.word_ext hz
  have heq := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hx
  have hbad := guard_byte_eq_zero input hbyte
  rw [← heq] at hbad
  exact (by decide : UInt256.eq (UInt256.ofNat 7) (UInt256.ofNat 7) ≠ UInt256.ofNat 0) hbad

private theorem guard_fallback_dest : Decode.isValidJumpDest submissionBytecode 272 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 176 (by rfl)

private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 106 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 64 (by rfl)

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with pc := UInt256.ofNat 106, stack := [UInt256.ofNat 0] }

private def bytePrefix : List Located :=
  [DirectGuard.opAt 3837 .JUMPDEST (by exact GuardInstructionWindow.get 114),
   DirectGuard.pushAt 3838 0 0 (by exact GuardInstructionWindow.get 115),
   DirectGuard.opAt 3839 .CALLDATALOAD (by exact GuardInstructionWindow.get 116),
   DirectGuard.pushAt 3840 0 0 (by exact GuardInstructionWindow.get 117),
   DirectGuard.opAt 3841 .BYTE (by exact GuardInstructionWindow.get 118),
   DirectGuard.pushAt 3842 1 7 (by exact GuardInstructionWindow.get 119),
   DirectGuard.opAt 3843 .XOR (by exact GuardInstructionWindow.get 120),
   DirectGuard.pushAt 3844 2 5155 (by exact GuardInstructionWindow.get 121)]

private def sizePrefix : List Located :=
  [DirectGuard.pushAt 3846 0 0 (by exact GuardInstructionWindow.get 123),
   DirectGuard.pushAt 3847 17 342276208914615837337402008677671501826 (by exact GuardInstructionWindow.get 124),
   DirectGuard.opAt 3848 .CALLDATASIZE (by exact GuardInstructionWindow.get 125),
   DirectGuard.opAt 3849 .SHR (by exact GuardInstructionWindow.get 126),
   DirectGuard.pushAt 3850 1 1 (by exact GuardInstructionWindow.get 127),
   DirectGuard.opAt 3851 .AND (by exact GuardInstructionWindow.get 128),
   DirectGuard.pushAt 3852 1 106 (by exact GuardInstructionWindow.get 129)]

private def fallbackSuffix : List Located :=
  [DirectGuard.opAt 3854 .POP (by exact GuardInstructionWindow.get 131),
   DirectGuard.pushAt 3855 2 272 (by exact GuardInstructionWindow.get 132),
   DirectGuard.opAt 3856 .JUMP (by exact GuardInstructionWindow.get 133)]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 64 .JUMPDEST,
   DirectGuard.opAt 65 .POP]

private theorem run_byte_prefix (input : ByteArray) :
    DirectGuard.run bytePrefix (PatternedScan.stS input 4792 []) =
      some (PatternedScan.stS input 4803 [5155, byteValue input]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let v := UInt256.xor 7 b
  let l0 : Located := DirectGuard.opAt 3837 .JUMPDEST (by exact GuardInstructionWindow.get 114)
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 3837 4792 [] (by norm_num) (GuardInstructionWindow.pc 114))
    (PatternedScan.stepS_jumpdest input 4792 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 3838 0 0 (by exact GuardInstructionWindow.get 115)
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 3838 4793 [] (by norm_num) (GuardInstructionWindow.pc 115))
    (PatternedScan.stepS_push0 input 4793 [] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.opAt 3839 .CALLDATALOAD (by exact GuardInstructionWindow.get 116)
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 3839 4794 [0] (by norm_num) (GuardInstructionWindow.pc 116))
    (PatternedScan.stepS_calldataload input 4794 0 [] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.pushAt 3840 0 0 (by exact GuardInstructionWindow.get 117)
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 3840 4795 [w] (by norm_num) (GuardInstructionWindow.pc 117))
    (PatternedScan.stepS_push0 input 4795 [w] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 3841 .BYTE (by exact GuardInstructionWindow.get 118)
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 3841 4796 [0, w] (by norm_num) (GuardInstructionWindow.pc 118))
    (PatternedScan.stepS_byte input 4796 0 w [] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.pushAt 3842 1 7 (by exact GuardInstructionWindow.get 119)
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 3842 4797 [b] (by norm_num) (GuardInstructionWindow.pc 119))
    (PatternedScan.stepS_push input 4797 1 7 [b] (by simp) (by decide) (by decide) (by norm_num))
  let l6 : Located := DirectGuard.opAt 3843 .XOR (by exact GuardInstructionWindow.get 120)
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 3843 4799 [7, b] (by norm_num) (GuardInstructionWindow.pc 120))
    (PatternedScan.stepS_xor input 4799 7 b [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 3844 2 5155 (by exact GuardInstructionWindow.get 121)
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 3844 4800 [v] (by norm_num) (GuardInstructionWindow.pc 121))
    (PatternedScan.stepS_push input 4800 2 5155 [v] (by simp) (by decide) (by decide) (by norm_num))
  have hseq1 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have hseq2 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ hseq1 rfl h2
  have hseq3 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ hseq2 rfl h3
  have hseq4 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ hseq3 rfl h4
  have hseq5 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ hseq4 rfl h5
  have hseq6 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ hseq5 rfl h6
  have hseq7 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ hseq6 rfl h7
  have hv : v = byteValue input := by
    simp only [v, b, w, byteValue, Word.literal_eq_ofNat]
  rw [hv] at hseq7
  exact hseq7

@[simp] private theorem sizeHitPC4102 : Artifact.submissionArtifact.instructionPC 3846 = 4804 := by
  exact GuardInstructionWindow.pc 123

@[simp] private theorem sizeHitPC4103 : Artifact.submissionArtifact.instructionPC 3847 = 4805 := by
  exact GuardInstructionWindow.pc 124

@[simp] private theorem sizeHitPC4106 : Artifact.submissionArtifact.instructionPC 3848 = 4823 := by
  exact GuardInstructionWindow.pc 125

@[simp] private theorem sizeHitPC4107 : Artifact.submissionArtifact.instructionPC 3849 = 4824 := by
  exact GuardInstructionWindow.pc 126

@[simp] private theorem sizeHitPC4108 : Artifact.submissionArtifact.instructionPC 3850 = 4825 := by
  exact GuardInstructionWindow.pc 127

@[simp] private theorem sizeHitPC4109 : Artifact.submissionArtifact.instructionPC 3851 = 4827 := by
  exact GuardInstructionWindow.pc 128

@[simp] private theorem sizeHitPC4110 : Artifact.submissionArtifact.instructionPC 3852 = 4828 := by
  exact GuardInstructionWindow.pc 129

@[simp] private theorem sizeHitPC4111 : Artifact.submissionArtifact.instructionPC 3853 = 4830 := by
  exact GuardInstructionWindow.pc 130

@[simp] private theorem sizeHitPC4112 : Artifact.submissionArtifact.instructionPC 3854 = 4831 := by
  exact GuardInstructionWindow.pc 131

@[simp] private theorem sizeHitPC4113 : Artifact.submissionArtifact.instructionPC 3855 = 4832 := by
  exact GuardInstructionWindow.pc 132

@[simp] private theorem sizeHitPC4114 : Artifact.submissionArtifact.instructionPC 3856 = 4835 := by
  exact GuardInstructionWindow.pc 133

private def sizeBit (input : ByteArray) : UInt256 :=
  UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826
    (UInt256.ofNat input.size))

private theorem sizeBit_flag (input : ByteArray) : UInt256.isZero (sizeBit input) = sizeFlag input := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  simpa only [sizeBit, sizeFlag, Word.literal_eq_ofNat] using h

private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (PatternedScan.stS input 4804 []) =
      some (PatternedScan.stS input 4830 [106, sizeBit input, 0]) := by
  simp (config := {maxSteps := 400000}) [sizePrefix, sizeBit, DirectGuard.opAt,
    DirectGuard.pushAt, DirectGuard.wfOp, PatternedScan.stS, initialState,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

private theorem run_byte_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run [DirectGuard.opAt 3845 .JUMPI (by exact GuardInstructionWindow.get 122)] (PatternedScan.stS input 4803 [5155, byteValue input]) =
      some (AbcArm.armEntry input) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 3845 .JUMPI (by exact GuardInstructionWindow.get 122))
    (PatternedScan.pcFactS input 3845 4803 [5155, byteValue input] (by norm_num) (GuardInstructionWindow.pc 122))
    (PatternedScan.stepS_jumpi_taken input 4803 5155 5155 (byteValue input) []
      (by simp) (by norm_num) (by simpa using Word.literal_eq_ofNat _) (byteValue_true input hbyte) AbcArm.arm_dest)

private theorem run_byte_fall (input : ByteArray) :
    DirectGuard.run [DirectGuard.opAt 3845 .JUMPI (by exact GuardInstructionWindow.get 122)] (PatternedScan.stS input 4803 [5155, UInt256.ofNat 0]) =
      some (PatternedScan.stS input 4804 []) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 3845 .JUMPI (by exact GuardInstructionWindow.get 122))
    (PatternedScan.pcFactS input 3845 4803 [5155, UInt256.ofNat 0] (by norm_num) (GuardInstructionWindow.pc 122))
    (PatternedScan.stepS_jumpi_fall input 4803 5155 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))

private theorem run_size_match (input : ByteArray) (hc : UInt256.isTrue (sizeBit input)) :
    DirectGuard.run [DirectGuard.opAt 3853 .JUMPI (by exact GuardInstructionWindow.get 130)]
      (PatternedScan.stS input 4830 [106, sizeBit input, 0]) =
      some (PatternedScan.stS input 106 [0]) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 3853 .JUMPI (by exact GuardInstructionWindow.get 130))
    (PatternedScan.pcFactS input 3853 4830 [106, sizeBit input, 0] (by norm_num) sizeHitPC4111)
    (PatternedScan.stepS_jumpi_taken input 4830 106 106 (sizeBit input) [0]
      (by simp) (by norm_num) (by rfl) hc guard_match_dest)

private theorem run_size_fall (input : ByteArray) (hc : ¬ UInt256.isTrue (sizeBit input)) :
    DirectGuard.run [DirectGuard.opAt 3853 .JUMPI (by exact GuardInstructionWindow.get 130)]
      (PatternedScan.stS input 4830 [106, sizeBit input, 0]) =
      some (PatternedScan.stS input 4831 [0]) := by
  exact PatternedScan.blockOfS (DirectGuard.opAt 3853 .JUMPI (by exact GuardInstructionWindow.get 130))
    (PatternedScan.pcFactS input 3853 4830 [106, sizeBit input, 0] (by norm_num) sizeHitPC4111)
    (PatternedScan.stepS_jumpi_fall input 4830 106 (sizeBit input) [0]
      (by simp) (by norm_num) hc)

private theorem run_fallback_suffix (input : ByteArray) :
    DirectGuard.run fallbackSuffix (PatternedScan.stS input 4831 [0]) =
      some (DirectGuard.fallbackState input) := by
  let l0 : Located := DirectGuard.opAt 3854 .POP (by exact GuardInstructionWindow.get 131)
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 3854 4831 [0] (by norm_num) sizeHitPC4112)
    (PatternedScan.stepS_pop input 4831 0 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 3855 2 272 (by exact GuardInstructionWindow.get 132)
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 3855 4832 [] (by norm_num) sizeHitPC4113)
    (PatternedScan.stepS_push input 4832 2 272 [] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 3856 .JUMP (by exact GuardInstructionWindow.get 133)
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 3856 4835 [272] (by norm_num) sizeHitPC4114)
    (PatternedScan.stepS_jump input 4835 272 272 [] (by simp) (by norm_num) (by rfl) guard_fallback_dest)
  have h01 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  exact Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ h01 rfl h2

private theorem run_guard_match_tail (input : ByteArray) :
    DirectGuard.run guardMatchTail (guardJumpState input) =
      some (PatternedScan.patternedEntry input) := by
  simp
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     guardJumpState, DirectGuard.guardEntry, PatternedScan.patternedEntry,
     DirectGuard.atPC, PatternedScan.atPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

private def gasSteps_byte_match (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.stS input 4804 []) := by
  have hp := run_byte_prefix input
  rw [byteValue_zero input hbyte] at hp
  exact (sound bytePrefix hp).trans (sound _ (run_byte_fall input))

private def gasSteps_byte_fail (input : ByteArray)
    (hbyte : DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (AbcArm.armEntry input) :=
  (sound bytePrefix (run_byte_prefix input)).trans (sound _ (run_byte_fail input hbyte))

private def gasSteps_size_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) :
    GasSteps (PatternedScan.stS input 4804 []) (DirectGuard.fallbackState input) := by
  have hf := sizeFlag_fail input hfit hbad
  rw [← sizeBit_flag] at hf
  have hc : ¬ UInt256.isTrue (sizeBit input) := by
    intro ht
    change (sizeBit input).toNat ≠ 0 at ht
    rw [UInt256.isZero, if_neg ht] at hf
    exact (by decide : UInt256.ofNat 0 ≠ UInt256.ofNat 1) hf
  exact (sound sizePrefix (run_size_prefix input)).trans
    ((sound _ (run_size_fall input hc)).trans (sound fallbackSuffix (run_fallback_suffix input)))


private def gasSteps_size_match (input : ByteArray) (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) :
    GasSteps (PatternedScan.stS input 4804 []) (PatternedScan.patternedEntry input) := by
  have hf := sizeFlag_hit input hsize
  rw [← sizeBit_flag] at hf
  have hc : UInt256.isTrue (sizeBit input) := by
    change (sizeBit input).toNat ≠ 0
    intro hz
    rw [UInt256.isZero, if_pos hz] at hf
    exact (by decide : UInt256.ofNat 1 ≠ UInt256.ofNat 0) hf
  exact (sound sizePrefix (run_size_prefix input)).trans
    ((sound _ (run_size_match input hc)).trans (sound guardMatchTail (run_guard_match_tail input)))

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size)
    (hnabc : input ≠ AbcInputData.abcInput)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) := by
  by_cases hbyte : DirectGuard.firstByte input = 7
  · have hs : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by
      rcases hbad with hs | hb
      · exact hs
      · exact False.elim (hb hbyte)
    exact (gasSteps_byte_match input hbyte).trans (gasSteps_size_fail input hfit hs)
  · exact (gasSteps_byte_fail input hbyte).trans (AbcArm.gasSteps_miss input hfit hpositive hnabc)

def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (gasSteps_byte_match input hbyte).trans (gasSteps_size_match input hsize)

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizeDispatchPath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize hbyte))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size)
    (hnabc : input ≠ AbcInputData.abcInput)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) ∨
      DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizeDispatchPath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hpositive hnabc hbad))

/-- Reaching the `abc` arm: the entry size classifier misses (3 is not 256, 376 or 1000)
and the byte-0 gate misses ('a' = 0x61 ≠ 7), so the byte-0 `JUMPI` lands on the arm (pc 5129). -/
def gasSteps_abc_entry (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = AbcInputData.abcInput) :
    GasSteps (initialState submissionBytecode input 0) (AbcArm.armEntry input) := by
  have hsize : input.size = 3 := by rw [heq]; rfl
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  -- `ByteArray.toList` is well-founded, so `decide` cannot evaluate `firstByte abcInput`;
  -- go through the byte-0 of the loaded word instead (`readWord abcInput 0 = abcWord`).
  have hbyte : DirectGuard.firstByte input ≠ 7 := by
    intro h7
    have h := firstByte_eq_byteAt input
    rw [heq, AbcRecognition.readWord_abcInput] at h
    rw [heq] at h7
    rw [h7] at h
    revert h; decide
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizeDispatchPath input)
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_byte_fail input hbyte))

/-- Empty calldata reaches the same tiny-input arm before initialization. -/
def gasSteps_empty_entry (input : ByteArray) (hfit : CalldataFits input)
    (heq : input = ByteArray.empty) :
    GasSteps (initialState submissionBytecode input 0) (AbcArm.armEntry input) := by
  have hsize : input.size = 0 := by rw [heq]; rfl
  have hbyte : DirectGuard.firstByte input ≠ 7 := by
    subst input
    simp [DirectGuard.firstByte, YulSemantics.EVM.byteFrom,
      YulEvmCompiler.ByteArray.toList_eq_data]
  exact (Execution.gasSteps_start input).trans
    ((sound (DirectGuard.sizeDispatchPath input)
        (DirectGuard.run_size_fail input hfit (by omega) (by omega) (by omega))).trans
      (gasSteps_byte_fail input hbyte))


end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
