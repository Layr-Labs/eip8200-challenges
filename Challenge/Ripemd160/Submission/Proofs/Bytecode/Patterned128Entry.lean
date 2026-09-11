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

/- The failure path stops at JUMPI.  It must not include the success suffix:
   a taken JUMPI changes the PC to 360, so the next located instruction would
   fail the PC check. -/
@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 59 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 60 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide









@[simp] private theorem entryPC4146 : Artifact.submissionArtifact.instructionPC 4126 = 5163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4147 : Artifact.submissionArtifact.instructionPC 4127 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4148 : Artifact.submissionArtifact.instructionPC 4128 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4149 : Artifact.submissionArtifact.instructionPC 4129 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4150 : Artifact.submissionArtifact.instructionPC 4130 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4151 : Artifact.submissionArtifact.instructionPC 4131 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4152 : Artifact.submissionArtifact.instructionPC 4132 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4153 : Artifact.submissionArtifact.instructionPC 4132 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4154 : Artifact.submissionArtifact.instructionPC 4133 = 5171 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4155 : Artifact.submissionArtifact.instructionPC 4134 = 5174 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4156 : Artifact.submissionArtifact.instructionPC 4135 = 5175 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4157 : Artifact.submissionArtifact.instructionPC 4136 = 5176 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4158 : Artifact.submissionArtifact.instructionPC 4137 = 5178 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4166 : Artifact.submissionArtifact.instructionPC 4119 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4167 : Artifact.submissionArtifact.instructionPC 4120 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4168 : Artifact.submissionArtifact.instructionPC 4121 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4169 : Artifact.submissionArtifact.instructionPC 4122 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4170 : Artifact.submissionArtifact.instructionPC 4123 = 5159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4171 : Artifact.submissionArtifact.instructionPC 4124 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4172 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4173 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4174 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4175 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4176 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4177 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4178 : Artifact.submissionArtifact.instructionPC 4125 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide





@[simp] private theorem entryOr00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by rfl

@[simp] private theorem entryOr01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr11 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

private def guardJumpPath : List Located := []

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4119 .JUMPDEST,
   DirectGuard.pushAt 4120 16 1329227995784915882199236691173048320,
   DirectGuard.opAt 4121 .CALLDATASIZE,
   DirectGuard.opAt 4122 .SHR,
   DirectGuard.pushAt 4123 1 1,
   DirectGuard.opAt 4124 .AND,
   DirectGuard.opAt 4125 .ISZERO]

private def guardBytePrefix : List Located :=
  [DirectGuard.pushAt 4126 0 0,
   DirectGuard.opAt 4127 .CALLDATALOAD,
   DirectGuard.pushAt 4128 0 0,
   DirectGuard.opAt 4129 .BYTE,
   DirectGuard.pushAt 4130 1 7,
   DirectGuard.opAt 4131 .XOR,
   DirectGuard.opAt 4132 .OR,
   DirectGuard.pushAt 4133 2 360]

private def guardBytePath : List Located := guardBytePrefix ++ [DirectGuard.opAt 4134 .JUMPI]

private def guardCheckPath : List Located := guardJumpPath ++ guardSizePath ++ guardBytePath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4135 0 0,
   DirectGuard.pushAt 4136 1 98,
   DirectGuard.opAt 4137 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 98
    stack := [UInt256.ofNat 0] }

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

private theorem guard_byte_eq_one (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    UInt256.eq (UInt256.ofNat 7)
        (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)) =
      UInt256.ofNat 1 := by
  rw [firstByte_eq_byteAt]
  unfold UInt256.eq
  simp [hbyte]

private theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 360 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 98 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5139 []
private def byteEntry (input : ByteArray) (flag : UInt256) : State :=
  PatternedScan.stS input 5163 [flag]
private def byteDone (input : ByteArray) : State := PatternedScan.stS input 5175 []

private theorem run_guard_jump (input : ByteArray) :
    DirectGuard.run guardJumpPath (DirectGuard.guardEntry input) = some (sizeEntry input) := by
  rfl

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (byteEntry input (sizeFlag input)) := by
  let m : UInt256 := 1329227995784915882199236691173048320
  let x : UInt256 := UInt256.ofNat input.size
  let shifted : UInt256 := UInt256.shiftRight m x
  let bit : UInt256 := UInt256.land 1 shifted
  let l0 : Located := DirectGuard.opAt 4119 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4119 5139 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5139 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4120 16 1329227995784915882199236691173048320
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4120 5140 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5140 16 1329227995784915882199236691173048320 [] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4121 .CALLDATASIZE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4121 5157 [m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5157 [m] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4122 .SHR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4122 5158 [x, m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shr input 5158 x m [] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.pushAt 4123 1 1
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4123 5159 [shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5159 1 1 [shifted] (by simp) (by decide) (by decide) (by norm_num))
  let l7 : Located := DirectGuard.opAt 4124 .AND
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4124 5161 [1, shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_and input 5161 1 shifted [] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.opAt 4125 .ISZERO
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4125 5162 [bit] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_iszero input 5162 bit [] (by simp) (by norm_num))
  have h01 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have h03 := Stepper.runLocatedBlock_append [l0, l1] [l3] _ _ _ h01 rfl h3
  have h05 := Stepper.runLocatedBlock_append [l0, l1, l3] [l5] _ _ _ h03 rfl h5
  have h06 := Stepper.runLocatedBlock_append [l0, l1, l3, l5] [l6] _ _ _ h05 rfl h6
  have h07 := Stepper.runLocatedBlock_append [l0, l1, l3, l5, l6] [l7] _ _ _ h06 rfl h7
  have h08 := Stepper.runLocatedBlock_append [l0, l1, l3, l5, l6, l7] [l8] _ _ _ h07 rfl h8
  have hf : UInt256.isZero bit = sizeFlag input := by
    have h := SizeLookupFlag.flag x
    rw [SizeLookupFlag.mask_literal] at h
    simpa only [bit, shifted, m, x, sizeFlag, Word.literal_eq_ofNat] using h
  rw [hf] at h08
  exact h08


/- Raw XOR is zero exactly on a byte match; the branch only needs truth, not 0/1. -/
private def byteFlag (input : ByteArray) (flag : UInt256) : UInt256 :=
  UInt256.lor (UInt256.xor (UInt256.ofNat 7)
    (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0))) flag

private theorem byteFlag_true (input : ByteArray) (flag : UInt256)
    (hflag : flag = UInt256.ofNat 1 ∨
      (flag = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7)) :
    UInt256.isTrue (byteFlag input flag) := by
  intro hz
  unfold byteFlag at hz
  rcases hflag with hflag | ⟨hflag, hbyte⟩
  · rw [hflag, Word.word_toNat_lor] at hz
    have ht := congrArg (fun n : Nat => n.testBit 0) hz
    simp [Word.word_toNat_ofNat, Nat.testBit_or] at ht
  · rw [hflag, Word.word_toNat_lor] at hz
    have hxNat : (UInt256.xor (UInt256.ofNat 7)
        (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0))).toNat = 0 := by
      simpa [Word.word_toNat_ofNat] using hz
    have hx : UInt256.xor (UInt256.ofNat 7)
        (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)) = 0 :=
      Word.word_ext hxNat
    have heq := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp hx
    have hbad := guard_byte_eq_zero input hbyte
    rw [← heq] at hbad
    exact (by decide : UInt256.eq (UInt256.ofNat 7) (UInt256.ofNat 7) ≠ UInt256.ofNat 0) hbad

private theorem byteFlag_zero (input : ByteArray) (hbyte : DirectGuard.firstByte input = 7) :
    byteFlag input (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  unfold byteFlag
  rw [firstByte_eq_byteAt, hbyte]
  decide

private theorem run_guard_byte_prefix (input : ByteArray) (flag : UInt256) :
    DirectGuard.run guardBytePrefix (byteEntry input flag) =
      some (PatternedScan.stS input 5174 [360, byteFlag input flag]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let z := UInt256.xor 7 b
  let f := UInt256.lor z flag
  let l0 : Located := DirectGuard.pushAt 4126 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4126 5163 [flag] (by norm_num) entryPC4146)
    (PatternedScan.stepS_push0 input 5163 [flag] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4127 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4127 5164 [0, flag] (by norm_num) entryPC4147)
    (PatternedScan.stepS_calldataload input 5164 0 [flag] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4128 0 0
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4128 5165 [w, flag] (by norm_num) entryPC4148)
    (PatternedScan.stepS_push0 input 5165 [w, flag] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4129 .BYTE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4129 5166 [0, w, flag] (by norm_num) entryPC4149)
    (PatternedScan.stepS_byte input 5166 0 w [flag] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.pushAt 4130 1 7
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4130 5167 [b, flag] (by norm_num) entryPC4150)
    (PatternedScan.stepS_push input 5167 1 7 [b, flag] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4131 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4131 5169 [7, b, flag] (by norm_num) entryPC4151)
    (PatternedScan.stepS_xor input 5169 7 b [flag] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4132 .OR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4132 5170 [z, flag] (by norm_num) entryPC4152)
    (PatternedScan.stepS_or input 5170 z flag [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4133 2 360
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4133 5171 [f] (by norm_num) entryPC4154)
    (PatternedScan.stepS_push input 5171 2 360 [f] (by simp) (by decide) (by decide) (by norm_num))
  have h_0_2 := Stepper.runLocatedBlock_append
    [l0] [l1] _ _ _ h0 rfl h1
  have h_2_4 := Stepper.runLocatedBlock_append
    [l2] [l3] _ _ _ h2 rfl h3
  have h_0_4 := Stepper.runLocatedBlock_append
    [l0, l1] [l2, l3] _ _ _ h_0_2 rfl h_2_4
  have h_4_6 := Stepper.runLocatedBlock_append
    [l4] [l5] _ _ _ h4 rfl h5
  have h_6_8 := Stepper.runLocatedBlock_append
    [l6] [l7] _ _ _ h6 rfl h7
  have h_4_8 := Stepper.runLocatedBlock_append
    [l4, l5] [l6, l7] _ _ _ h_4_6 rfl h_6_8
  have h_0_8 := Stepper.runLocatedBlock_append
    [l0, l1, l2, l3] [l4, l5, l6, l7] _ _ _ h_0_4 rfl h_4_8
  have hf : f = byteFlag input flag := by
    simp only [f, z, b, w, byteFlag, Word.literal_eq_ofNat]
  rw [hf] at h_0_8
  exact h_0_8

private theorem run_guard_byte_fail (input : ByteArray) (flag : UInt256)
    (hflag : flag = UInt256.ofNat 1 ∨
      (flag = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7)) :
    DirectGuard.run guardBytePath (byteEntry input flag) = some (DirectGuard.fallbackState input) := by
  have ht := byteFlag_true input flag hflag
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4134 .JUMPI)
    (PatternedScan.pcFactS input 4134 5174 [360, byteFlag input flag] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_taken input 5174 360 360 (byteFlag input flag) []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 360)
      ht guard_fallback_dest)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4134 .JUMPI] _ _ _ (run_guard_byte_prefix input flag) rfl hj

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (DirectGuard.fallbackState input) := by
  have hf : sizeFlag input = UInt256.ofNat 1 ∨
      (sizeFlag input = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7) := by
    by_cases hs : input.size = 56 ∨ input.size = 120 ∨ input.size = 63
    · exact Or.inr ⟨sizeFlag_hit input hs, by rcases hbad with h | h <;> tauto⟩
    · exact Or.inl (sizeFlag_fail input hfit (by tauto))
  have hjs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardJumpPath guardSizePath _ _ _ (run_guard_jump input) rfl (run_guard_size input)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    (guardJumpPath ++ guardSizePath) guardBytePath _ _ _ hjs rfl
    (run_guard_byte_fail input (sizeFlag input) hf)

private theorem run_guard_byte_match (input : ByteArray)
    (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run (guardBytePath ++ guardMatchSuffix)
      (byteEntry input (UInt256.ofNat 0)) = some (guardJumpState input) := by
  have hf := byteFlag_zero input hbyte
  have hprefix : DirectGuard.run guardBytePrefix (byteEntry input (UInt256.ofNat 0)) =
      some (PatternedScan.stS input 5174 [360, UInt256.ofNat 0]) := by
    simpa only [hf] using run_guard_byte_prefix input (UInt256.ofNat 0)
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4134 .JUMPI)
    (PatternedScan.pcFactS input 4134 5174 [360, UInt256.ofNat 0] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_fall input 5174 360 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4135 0 0)
    (PatternedScan.pcFactS input 4135 5175 [] (by norm_num) entryPC4156)
    (PatternedScan.stepS_push0 input 5175 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4136 1 98)
    (PatternedScan.pcFactS input 4136 5176 [0] (by norm_num) entryPC4157)
    (PatternedScan.stepS_push input 5176 1 98 [0] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4137 .JUMP)
    (PatternedScan.pcFactS input 4137 5178 [98, 0] (by norm_num) entryPC4158)
    (PatternedScan.stepS_jump input 5178 98 98 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 98) guard_match_dest)
  have hpj := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4134 .JUMPI] _ _ _ hprefix rfl hj
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4135 0 0] [DirectGuard.pushAt 4136 1 98] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4135 0 0, DirectGuard.pushAt 4136 1 98]
    [DirectGuard.opAt 4137 .JUMP] _ _ _ h01 rfl h2
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePath guardMatchSuffix _ _ _ hpj rfl hs

private theorem run_guard_match_helper (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63)
    (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run (guardCheckPath ++ guardMatchSuffix)
      (DirectGuard.guardEntry input) = some (guardJumpState input) := by
  have hs : DirectGuard.run guardSizePath (sizeEntry input) =
      some (byteEntry input (UInt256.ofNat 0)) := by
    simpa only [sizeFlag_hit input hsize] using run_guard_size input
  have hjs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardJumpPath guardSizePath _ _ _ (run_guard_jump input) rfl hs
  simpa only [guardCheckPath, List.append_assoc] using
    (Challenge.EvmProof.Stepper.runLocatedBlock_append
      (guardJumpPath ++ guardSizePath) (guardBytePath ++ guardMatchSuffix) _ _ _ hjs rfl
      (run_guard_byte_match input hbyte))

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

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  sound guardCheckPath (run_guard_fail input hfit hbad)

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match_helper input hfit hsize hbyte)).trans
    (sound guardMatchTail (run_guard_match_tail input))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize hbyte))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
