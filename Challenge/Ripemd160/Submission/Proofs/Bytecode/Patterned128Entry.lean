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

/-! The appended 56/120/128-byte guard and its bridge into the patterned scan. -/

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
   a taken JUMPI changes the PC to 368, so the next located instruction would
   fail the PC check. -/
@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 59 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 60 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide









@[simp] private theorem entryPC4146 : Artifact.submissionArtifact.instructionPC 4138 = 5153 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4147 : Artifact.submissionArtifact.instructionPC 4139 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4148 : Artifact.submissionArtifact.instructionPC 4140 = 5155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4149 : Artifact.submissionArtifact.instructionPC 4141 = 5156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4150 : Artifact.submissionArtifact.instructionPC 4142 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4151 : Artifact.submissionArtifact.instructionPC 4143 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4152 : Artifact.submissionArtifact.instructionPC 4144 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4153 : Artifact.submissionArtifact.instructionPC 4144 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4154 : Artifact.submissionArtifact.instructionPC 4145 = 5162 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4155 : Artifact.submissionArtifact.instructionPC 4146 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4156 : Artifact.submissionArtifact.instructionPC 4147 = 5166 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4157 : Artifact.submissionArtifact.instructionPC 4148 = 5167 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4158 : Artifact.submissionArtifact.instructionPC 4149 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4166 : Artifact.submissionArtifact.instructionPC 4131 = 5128 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4167 : Artifact.submissionArtifact.instructionPC 4132 = 5129 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4168 : Artifact.submissionArtifact.instructionPC 4133 = 5147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4169 : Artifact.submissionArtifact.instructionPC 4134 = 5148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4170 : Artifact.submissionArtifact.instructionPC 4135 = 5149 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4171 : Artifact.submissionArtifact.instructionPC 4136 = 5151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4172 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4173 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4174 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4175 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4176 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4177 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4178 : Artifact.submissionArtifact.instructionPC 4137 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide





@[simp] private theorem entryOr00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by rfl

@[simp] private theorem entryOr01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr11 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

private def guardJumpPath : List Located := []

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4131 .JUMPDEST,
   DirectGuard.pushAt 4132 17 341611594916723379336350472086086483968,
   DirectGuard.opAt 4133 .CALLDATASIZE,
   DirectGuard.opAt 4134 .SHR,
   DirectGuard.pushAt 4135 1 1,
   DirectGuard.opAt 4136 .AND,
   DirectGuard.opAt 4137 .ISZERO]

private def guardBytePrefix : List Located :=
  [DirectGuard.pushAt 4138 0 0,
   DirectGuard.opAt 4139 .CALLDATALOAD,
   DirectGuard.pushAt 4140 0 0,
   DirectGuard.opAt 4141 .BYTE,
   DirectGuard.pushAt 4142 2 7,
   DirectGuard.opAt 4143 .XOR,
   DirectGuard.opAt 4144 .OR,
   DirectGuard.pushAt 4145 2 368]

private def guardBytePath : List Located := guardBytePrefix ++ [DirectGuard.opAt 4146 .JUMPI]

private def guardCheckPath : List Located := guardJumpPath ++ guardSizePath ++ guardBytePath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4147 0 0,
   DirectGuard.pushAt 4148 1 101,
   DirectGuard.opAt 4149 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 101
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
    Decode.isValidJumpDest submissionBytecode 368 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5128 []
private def byteEntry (input : ByteArray) (flag : UInt256) : State :=
  PatternedScan.stS input 5153 [flag]
private def byteDone (input : ByteArray) : State := PatternedScan.stS input 5166 []

private theorem run_guard_jump (input : ByteArray) :
    DirectGuard.run guardJumpPath (DirectGuard.guardEntry input) = some (sizeEntry input) := by
  rfl

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (byteEntry input (sizeFlag input)) := by
  let m : UInt256 := 341611594916723379336350472086086483968
  let x : UInt256 := UInt256.ofNat input.size
  let shifted : UInt256 := UInt256.shiftRight m x
  let bit : UInt256 := UInt256.land 1 shifted
  let l0 : Located := DirectGuard.opAt 4131 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4131 5128 [] (by norm_num) entryPC4166)
    (PatternedScan.stepS_jumpdest input 5128 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4132 17 341611594916723379336350472086086483968
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4132 5129 [] (by norm_num) entryPC4167)
    (PatternedScan.stepS_push input 5129 17 341611594916723379336350472086086483968 [] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.opAt 4133 .CALLDATASIZE
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4133 5147 [m] (by norm_num) entryPC4168)
    (PatternedScan.stepS_calldatasize input 5147 [m] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4134 .SHR
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4134 5148 [x, m] (by norm_num) entryPC4169)
    (PatternedScan.stepS_shr input 5148 x m [] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.pushAt 4135 1 1
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4135 5149 [shifted] (by norm_num) entryPC4170)
    (PatternedScan.stepS_push input 5149 1 1 [shifted] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4136 .AND
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4136 5151 [1, shifted] (by norm_num) entryPC4171)
    (PatternedScan.stepS_and input 5151 1 shifted [] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4137 .ISZERO
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4137 5152 [bit] (by norm_num) entryPC4172)
    (PatternedScan.stepS_iszero input 5152 bit [] (by simp) (by norm_num))
  have h_1_3 := Stepper.runLocatedBlock_append
    [l1] [l2] _ _ _ h1 rfl h2
  have h_0_3 := Stepper.runLocatedBlock_append
    [l0] [l1, l2] _ _ _ h0 rfl h_1_3
  have h_3_5 := Stepper.runLocatedBlock_append
    [l3] [l4] _ _ _ h3 rfl h4
  have h_5_7 := Stepper.runLocatedBlock_append
    [l5] [l6] _ _ _ h5 rfl h6
  have h_3_7 := Stepper.runLocatedBlock_append
    [l3, l4] [l5, l6] _ _ _ h_3_5 rfl h_5_7
  have h_0_7 := Stepper.runLocatedBlock_append
    [l0, l1, l2] [l3, l4, l5, l6] _ _ _ h_0_3 rfl h_3_7
  have hf : UInt256.isZero bit = sizeFlag input := by
    have h := SizeLookupFlag.flag x
    rw [SizeLookupFlag.mask_literal] at h
    simpa only [bit, shifted, m, x, sizeFlag, Word.literal_eq_ofNat] using h
  rw [hf] at h_0_7
  exact h_0_7

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
      some (PatternedScan.stS input 5165 [368, byteFlag input flag]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let z := UInt256.xor 7 b
  let f := UInt256.lor z flag
  let l0 : Located := DirectGuard.pushAt 4138 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4138 5153 [flag] (by norm_num) entryPC4146)
    (PatternedScan.stepS_push0 input 5153 [flag] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4139 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4139 5154 [0, flag] (by norm_num) entryPC4147)
    (PatternedScan.stepS_calldataload input 5154 0 [flag] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4140 0 0
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4140 5155 [w, flag] (by norm_num) entryPC4148)
    (PatternedScan.stepS_push0 input 5155 [w, flag] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4141 .BYTE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4141 5156 [0, w, flag] (by norm_num) entryPC4149)
    (PatternedScan.stepS_byte input 5156 0 w [flag] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.pushAt 4142 2 7
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4142 5157 [b, flag] (by norm_num) entryPC4150)
    (PatternedScan.stepS_push input 5157 2 7 [b, flag] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4143 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4143 5160 [7, b, flag] (by norm_num) entryPC4151)
    (PatternedScan.stepS_xor input 5160 7 b [flag] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4144 .OR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4144 5161 [z, flag] (by norm_num) entryPC4152)
    (PatternedScan.stepS_or input 5161 z flag [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4145 2 368
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4145 5162 [f] (by norm_num) entryPC4154)
    (PatternedScan.stepS_push input 5162 2 368 [f] (by simp) (by decide) (by decide) (by norm_num))
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
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4146 .JUMPI)
    (PatternedScan.pcFactS input 4146 5165 [368, byteFlag input flag] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_taken input 5165 368 368 (byteFlag input flag) []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 368)
      ht guard_fallback_dest)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4146 .JUMPI] _ _ _ (run_guard_byte_prefix input flag) rfl hj

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 128) ∨
      DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (DirectGuard.fallbackState input) := by
  have hf : sizeFlag input = UInt256.ofNat 1 ∨
      (sizeFlag input = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7) := by
    by_cases hs : input.size = 56 ∨ input.size = 120 ∨ input.size = 128
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
      some (PatternedScan.stS input 5165 [368, UInt256.ofNat 0]) := by
    simpa only [hf] using run_guard_byte_prefix input (UInt256.ofNat 0)
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4146 .JUMPI)
    (PatternedScan.pcFactS input 4146 5165 [368, UInt256.ofNat 0] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_fall input 5165 368 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4147 0 0)
    (PatternedScan.pcFactS input 4147 5166 [] (by norm_num) entryPC4156)
    (PatternedScan.stepS_push0 input 5166 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4148 1 101)
    (PatternedScan.pcFactS input 4148 5167 [0] (by norm_num) entryPC4157)
    (PatternedScan.stepS_push input 5167 1 101 [0] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4149 .JUMP)
    (PatternedScan.pcFactS input 4149 5169 [101, 0] (by norm_num) entryPC4158)
    (PatternedScan.stepS_jump input 5169 101 101 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 101) guard_match_dest)
  have hpj := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4146 .JUMPI] _ _ _ hprefix rfl hj
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4147 0 0] [DirectGuard.pushAt 4148 1 101] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4147 0 0, DirectGuard.pushAt 4148 1 101]
    [DirectGuard.opAt 4149 .JUMP] _ _ _ h01 rfl h2
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePath guardMatchSuffix _ _ _ hpj rfl hs

private theorem run_guard_match_helper (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 128)
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 128) ∨
      DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  sound guardCheckPath (run_guard_fail input hfit hbad)

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match_helper input hfit hsize hbyte)).trans
    (sound guardMatchTail (run_guard_match_tail input))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 128) ∨
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
