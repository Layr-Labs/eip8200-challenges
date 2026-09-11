import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLengthMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntryLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternEntrySteps
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPattern128Hop

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
   a taken JUMPI changes the PC to 363, so the next located instruction would
   fail the PC check. -/
@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 59 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 60 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide









@[simp] private theorem entryPC4146 : Artifact.submissionArtifact.instructionPC 4131 = 5157 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4147 : Artifact.submissionArtifact.instructionPC 4132 = 5158 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4148 : Artifact.submissionArtifact.instructionPC 4133 = 5159 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4149 : Artifact.submissionArtifact.instructionPC 4134 = 5160 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4150 : Artifact.submissionArtifact.instructionPC 4135 = 5161 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4151 : Artifact.submissionArtifact.instructionPC 4136 = 5163 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4152 : Artifact.submissionArtifact.instructionPC 4137 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4153 : Artifact.submissionArtifact.instructionPC 4137 = 5164 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4154 : Artifact.submissionArtifact.instructionPC 4138 = 5165 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4155 : Artifact.submissionArtifact.instructionPC 4139 = 5168 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4156 : Artifact.submissionArtifact.instructionPC 4140 = 5169 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4157 : Artifact.submissionArtifact.instructionPC 4141 = 5170 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4158 : Artifact.submissionArtifact.instructionPC 4142 = 5172 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4166 : Artifact.submissionArtifact.instructionPC 4119 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4167 : Artifact.submissionArtifact.instructionPC 4120 = 5143 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4168 : Artifact.submissionArtifact.instructionPC 4121 = 5144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4169 : Artifact.submissionArtifact.instructionPC 4122 = 5146 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4170 : Artifact.submissionArtifact.instructionPC 4123 = 5147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4171 : Artifact.submissionArtifact.instructionPC 4124 = 5148 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4172 : Artifact.submissionArtifact.instructionPC 4125 = 5150 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4173 : Artifact.submissionArtifact.instructionPC 4126 = 5151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4174 : Artifact.submissionArtifact.instructionPC 4126 = 5151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4175 : Artifact.submissionArtifact.instructionPC 4127 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4176 : Artifact.submissionArtifact.instructionPC 4128 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4177 : Artifact.submissionArtifact.instructionPC 4129 = 5155 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4178 : Artifact.submissionArtifact.instructionPC 4130 = 5156 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide





@[simp] private theorem entryOr00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by rfl

@[simp] private theorem entryOr01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr11 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

private def guardJumpPath : List Located := []

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4119 .JUMPDEST,
   DirectGuard.opAt 4120 .CALLDATASIZE,
   DirectGuard.pushAt 4121 1 64,
   DirectGuard.opAt 4122 .NOT,
   DirectGuard.opAt 4123 .AND,
   DirectGuard.pushAt 4124 1 56,
   DirectGuard.opAt 4125 .EQ,
   DirectGuard.opAt 4126 .CALLDATASIZE,
   DirectGuard.pushAt 4127 1 63,
   DirectGuard.opAt 4128 .EQ,
   DirectGuard.opAt 4129 .OR,
   DirectGuard.opAt 4130 .ISZERO]

private def guardBytePrefix : List Located :=
  [DirectGuard.pushAt 4131 0 0,
   DirectGuard.opAt 4132 .CALLDATALOAD,
   DirectGuard.pushAt 4133 0 0,
   DirectGuard.opAt 4134 .BYTE,
   DirectGuard.pushAt 4135 1 7,
   DirectGuard.opAt 4136 .XOR,
   DirectGuard.opAt 4137 .OR,
   DirectGuard.pushAt 4138 2 5262]

private def guardBytePath : List Located := guardBytePrefix ++ [DirectGuard.opAt 4139 .JUMPI]

private def guardCheckPath : List Located := guardJumpPath ++ guardSizePath ++ guardBytePath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4140 0 0,
   DirectGuard.pushAt 4141 1 101,
   DirectGuard.opAt 4142 .JUMP]

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
    Decode.isValidJumpDest submissionBytecode 5262 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4168 (by rfl)

private theorem generic_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 363 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5142 []
private def byteEntry (input : ByteArray) (flag : UInt256) : State :=
  PatternedScan.stS input 5157 [flag]
private def byteDone (input : ByteArray) : State := PatternedScan.stS input 5169 []

private theorem run_guard_jump (input : ByteArray) :
    DirectGuard.run guardJumpPath (DirectGuard.guardEntry input) = some (sizeEntry input) := by
  rfl

private theorem step_size_not (input : ByteArray) (pc : Nat)
    (a : UInt256) (rest : List UInt256)
    (hlen : rest.length + 1 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    Stepper.runInstr (.op .NOT) (PatternedScan.stS input pc (a :: rest)) =
      some (PatternedScan.stS input (pc + 1) (UInt256.lnot a :: rest)) := by
  unfold Stepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Word.succ_ofNat hpc]

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (byteEntry input (sizeFlag input)) := by
  let x : UInt256 := UInt256.ofNat input.size
  let nm : UInt256 := UInt256.lnot 64
  let masked : UInt256 := UInt256.land nm x
  let pair : UInt256 := UInt256.lor (UInt256.eq 120 x) (UInt256.eq 56 x)
  let v128 : UInt256 := UInt256.eq 63 x
  let both : UInt256 := UInt256.lor v128 pair
  let l0 : Located := DirectGuard.opAt 4119 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4119 5142 [] (by norm_num)
      entryPC4166)
    (PatternedScan.stepS_jumpdest input 5142 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4120 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4120 5143 [] (by norm_num)
      entryPC4167)
    (PatternedScan.stepS_calldatasize input 5143 [] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4121 1 64
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4121 5144 [x] (by norm_num)
      entryPC4168)
    (PatternedScan.stepS_push input 5144 1 64 [x] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4122 .NOT
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4122 5146 [64, x] (by norm_num)
      entryPC4169)
    (step_size_not input 5146 64 [x] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4123 .AND
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4123 5147 [nm, x] (by norm_num)
      entryPC4170)
    (PatternedScan.stepS_and input 5147 nm x [] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.pushAt 4124 1 56
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4124 5148 [masked] (by norm_num)
      entryPC4171)
    (PatternedScan.stepS_push input 5148 1 56 [masked] (by simp) (by decide) (by decide) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4125 .EQ
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4125 5150 [56, masked] (by norm_num)
      entryPC4172)
    (PatternedScan.stepS_eq input 5150 56 masked [] (by simp) (by norm_num))
  have hp : UInt256.eq (56 : UInt256) masked = pair := PairLengthMask.flags x
  rw [hp] at h6
  let l7 : Located := DirectGuard.opAt 4126 .CALLDATASIZE
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4126 5151 [pair] (by norm_num)
      entryPC4174)
    (PatternedScan.stepS_calldatasize input 5151 [pair] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.pushAt 4127 1 63
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4127 5152 [x, pair] (by norm_num)
      entryPC4175)
    (PatternedScan.stepS_push input 5152 1 63 [x, pair] (by simp) (by decide) (by decide) (by norm_num))
  let l9 : Located := DirectGuard.opAt 4128 .EQ
  have h9 := PatternedScan.blockOfS l9
    (PatternedScan.pcFactS input 4128 5154 [63, x, pair] (by norm_num)
      entryPC4176)
    (PatternedScan.stepS_eq input 5154 63 x [pair] (by simp) (by norm_num))
  let l10 : Located := DirectGuard.opAt 4129 .OR
  have h10 := PatternedScan.blockOfS l10
    (PatternedScan.pcFactS input 4129 5155 [v128, pair] (by norm_num)
      entryPC4177)
    (PatternedScan.stepS_or input 5155 v128 pair [] (by simp) (by norm_num))
  let l11 : Located := DirectGuard.opAt 4130 .ISZERO
  have h11 := PatternedScan.blockOfS l11
    (PatternedScan.pcFactS input 4130 5156 [both] (by norm_num)
      entryPC4178)
    (PatternedScan.stepS_iszero input 5156 both [] (by simp) (by norm_num))
  have h_1_3 := Stepper.runLocatedBlock_append
    [l1] [l2] _ _ _ h1 rfl h2
  have h_0_3 := Stepper.runLocatedBlock_append
    [l0] [l1, l2] _ _ _ h0 rfl h_1_3
  have h_4_6 := Stepper.runLocatedBlock_append
    [l4] [l5] _ _ _ h4 rfl h5
  have h_3_6 := Stepper.runLocatedBlock_append
    [l3] [l4, l5] _ _ _ h3 rfl h_4_6
  have h_0_6 := Stepper.runLocatedBlock_append
    [l0, l1, l2] [l3, l4, l5] _ _ _ h_0_3 rfl h_3_6
  have h_7_9 := Stepper.runLocatedBlock_append
    [l7] [l8] _ _ _ h7 rfl h8
  have h_6_9 := Stepper.runLocatedBlock_append
    [l6] [l7, l8] _ _ _ h6 rfl h_7_9
  have h_10_12 := Stepper.runLocatedBlock_append
    [l10] [l11] _ _ _ h10 rfl h11
  have h_9_12 := Stepper.runLocatedBlock_append
    [l9] [l10, l11] _ _ _ h9 rfl h_10_12
  have h_6_12 := Stepper.runLocatedBlock_append
    [l6, l7, l8] [l9, l10, l11] _ _ _ h_6_9 rfl h_9_12
  have h_0_12 := Stepper.runLocatedBlock_append
    [l0, l1, l2, l3, l4, l5] [l6, l7, l8, l9, l10, l11] _ _ _ h_0_6 rfl h_6_12
  have hv : UInt256.isZero both = sizeFlag input := by
    simp only [both, pair, v128, x, sizeFlag, Word.literal_eq_ofNat]
  rw [hv] at h_0_12
  exact h_0_12

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
      some (PatternedScan.stS input 5168 [5262, byteFlag input flag]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let z := UInt256.xor 7 b
  let f := UInt256.lor z flag
  let l0 : Located := DirectGuard.pushAt 4131 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4131 5157 [flag] (by norm_num) entryPC4146)
    (PatternedScan.stepS_push0 input 5157 [flag] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4132 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4132 5158 [0, flag] (by norm_num) entryPC4147)
    (PatternedScan.stepS_calldataload input 5158 0 [flag] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4133 0 0
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4133 5159 [w, flag] (by norm_num) entryPC4148)
    (PatternedScan.stepS_push0 input 5159 [w, flag] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4134 .BYTE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4134 5160 [0, w, flag] (by norm_num) entryPC4149)
    (PatternedScan.stepS_byte input 5160 0 w [flag] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.pushAt 4135 1 7
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4135 5161 [b, flag] (by norm_num) entryPC4150)
    (PatternedScan.stepS_push input 5161 1 7 [b, flag] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4136 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4136 5163 [7, b, flag] (by norm_num) entryPC4151)
    (PatternedScan.stepS_xor input 5163 7 b [flag] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4137 .OR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4137 5164 [z, flag] (by norm_num) entryPC4152)
    (PatternedScan.stepS_or input 5164 z flag [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4138 2 5262
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4138 5165 [f] (by norm_num) entryPC4154)
    (PatternedScan.stepS_push input 5165 2 5262 [f] (by simp) (by decide) (by decide) (by norm_num))
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
    DirectGuard.run guardBytePath (byteEntry input flag) =
      some (ShortPattern128Hop.missEntry input) := by
  have ht := byteFlag_true input flag hflag
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4139 .JUMPI)
    (PatternedScan.pcFactS input 4139 5168 [5262, byteFlag input flag] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_taken input 5168 5262 5262 (byteFlag input flag) []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 5262)
      ht guard_fallback_dest)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4139 .JUMPI] _ _ _ (run_guard_byte_prefix input flag) rfl hj

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (ShortPattern128Hop.missEntry input) := by
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
      some (PatternedScan.stS input 5168 [5262, UInt256.ofNat 0]) := by
    simpa only [hf] using run_guard_byte_prefix input (UInt256.ofNat 0)
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4139 .JUMPI)
    (PatternedScan.pcFactS input 4139 5168 [5262, UInt256.ofNat 0] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_fall input 5168 5262 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4140 0 0)
    (PatternedScan.pcFactS input 4140 5169 [] (by norm_num) entryPC4156)
    (PatternedScan.stepS_push0 input 5169 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4141 1 101)
    (PatternedScan.pcFactS input 4141 5170 [0] (by norm_num) entryPC4157)
    (PatternedScan.stepS_push input 5170 1 101 [0] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4142 .JUMP)
    (PatternedScan.pcFactS input 4142 5172 [101, 0] (by norm_num) entryPC4158)
    (PatternedScan.stepS_jump input 5172 101 101 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 101) guard_match_dest)
  have hpj := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4139 .JUMPI] _ _ _ hprefix rfl hj
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4140 0 0] [DirectGuard.pushAt 4141 1 101] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4140 0 0, DirectGuard.pushAt 4141 1 101]
    [DirectGuard.opAt 4142 .JUMP] _ _ _ h01 rfl h2
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
      DirectGuard.firstByte input ≠ 7)
    (hgen : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  (sound guardCheckPath (run_guard_fail input hfit hbad)).trans
    (ShortPattern128Hop.gasSteps_miss_generic input hfit hgen)

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

def gasSteps_hit128 (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  have hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7 :=
    Or.inl ⟨by omega, by omega, by omega⟩
  have htail : DirectGuard.run guardMatchTail
      (PatternedScan.stS input 101 [UInt256.ofNat 0]) =
      some (PatternedScan.patternedEntry input) := by
    simpa [guardJumpState, PatternedScan.stS, DirectGuard.guardEntry,
      DirectGuard.atPC] using run_guard_match_tail input
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      ((sound guardCheckPath (run_guard_fail input hfit hbad)).trans
        ((ShortPattern128Hop.gasSteps_miss_scan input hsize hbyte).trans
          (sound guardMatchTail htail))))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63) ∨
      DirectGuard.firstByte input ≠ 7)
    (hgen : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad hgen))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
