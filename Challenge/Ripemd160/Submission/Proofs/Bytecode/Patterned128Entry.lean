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









@[simp] private theorem entryPC4146 : Artifact.submissionArtifact.instructionPC 4090 = 5056 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4147 : Artifact.submissionArtifact.instructionPC 4091 = 5057 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4148 : Artifact.submissionArtifact.instructionPC 4092 = 5058 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4149 : Artifact.submissionArtifact.instructionPC 4093 = 5059 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4150 : Artifact.submissionArtifact.instructionPC 4094 = 5060 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4151 : Artifact.submissionArtifact.instructionPC 4095 = 5062 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4152 : Artifact.submissionArtifact.instructionPC 4096 = 5063 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4153 : Artifact.submissionArtifact.instructionPC 4096 = 5063 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4154 : Artifact.submissionArtifact.instructionPC 4097 = 5064 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4155 : Artifact.submissionArtifact.instructionPC 4098 = 5067 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4156 : Artifact.submissionArtifact.instructionPC 4099 = 5068 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4157 : Artifact.submissionArtifact.instructionPC 4100 = 5069 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4158 : Artifact.submissionArtifact.instructionPC 4101 = 5071 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4166 : Artifact.submissionArtifact.instructionPC 4081 = 5035 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4167 : Artifact.submissionArtifact.instructionPC 4082 = 5036 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4168 : Artifact.submissionArtifact.instructionPC 4084 = 5049 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4169 : Artifact.submissionArtifact.instructionPC 4086 = 5051 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4170 : Artifact.submissionArtifact.instructionPC 4087 = 5052 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4171 : Artifact.submissionArtifact.instructionPC 4088 = 5054 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4172 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4173 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4174 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4175 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4176 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4177 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4178 : Artifact.submissionArtifact.instructionPC 4089 = 5055 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide





@[simp] private theorem entryOr00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by rfl

@[simp] private theorem entryOr01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr11 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

private def guardJumpPath : List Located := []

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4081 .JUMPDEST,
   DirectGuard.pushAt 4082 10 4740813226943354766209,
   DirectGuard.pushAt 4083 1 56,
   DirectGuard.opAt 4084 .CALLDATASIZE,
   DirectGuard.opAt 4085 .SUB,
   DirectGuard.opAt 4086 .SHR,
   DirectGuard.pushAt 4087 1 1,
   DirectGuard.opAt 4088 .AND,
   DirectGuard.opAt 4089 .ISZERO]

private def guardBytePrefix : List Located :=
  [DirectGuard.pushAt 4090 0 0,
   DirectGuard.opAt 4091 .CALLDATALOAD,
   DirectGuard.pushAt 4092 0 0,
   DirectGuard.opAt 4093 .BYTE,
   DirectGuard.pushAt 4094 1 7,
   DirectGuard.opAt 4095 .XOR,
   DirectGuard.opAt 4096 .OR,
   DirectGuard.pushAt 4097 2 5269]

private def guardBytePath : List Located := guardBytePrefix ++ [DirectGuard.opAt 4098 .JUMPI]

private def guardCheckPath : List Located := guardJumpPath ++ guardSizePath ++ guardBytePath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4099 0 0,
   DirectGuard.pushAt 4100 1 98,
   DirectGuard.opAt 4101 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP]

private def stubPath : List Located :=
  [DirectGuard.opAt 4151 .JUMPDEST,
   DirectGuard.pushAt 4152 0 0,
   DirectGuard.opAt 4153 .CALLDATASIZE,
   DirectGuard.pushAt 4154 1 32,
   DirectGuard.opAt 4155 .EQ,
   DirectGuard.pushAt 4156 0 0,
   DirectGuard.opAt 4157 .CALLDATALOAD,
   DirectGuard.pushAt 4158 0 0,
   DirectGuard.opAt 4159 .BYTE,
   DirectGuard.pushAt 4160 1 7,
   DirectGuard.opAt 4161 .XOR,
   DirectGuard.opAt 4162 .ISZERO,
   DirectGuard.opAt 4163 .AND,
   DirectGuard.pushAt 4164 2 98,
   DirectGuard.opAt 4165 .JUMPI]

private def stubFailTail : List Located :=
  [DirectGuard.opAt 4166 .POP,
   DirectGuard.pushAt 4167 2 360,
   DirectGuard.opAt 4168 .JUMP]

private def stubFailPath : List Located := stubPath ++ stubFailTail

@[simp] private theorem stubPC4151 : Artifact.submissionArtifact.instructionPC 4151 = 5269 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4152 : Artifact.submissionArtifact.instructionPC 4152 = 5270 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4153 : Artifact.submissionArtifact.instructionPC 4153 = 5271 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4154 : Artifact.submissionArtifact.instructionPC 4154 = 5272 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4155 : Artifact.submissionArtifact.instructionPC 4155 = 5274 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4156 : Artifact.submissionArtifact.instructionPC 4156 = 5275 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4157 : Artifact.submissionArtifact.instructionPC 4157 = 5276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4158 : Artifact.submissionArtifact.instructionPC 4158 = 5277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4159 : Artifact.submissionArtifact.instructionPC 4159 = 5278 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4160 : Artifact.submissionArtifact.instructionPC 4160 = 5279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4161 : Artifact.submissionArtifact.instructionPC 4161 = 5281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4162 : Artifact.submissionArtifact.instructionPC 4162 = 5282 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4163 : Artifact.submissionArtifact.instructionPC 4163 = 5283 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4164 : Artifact.submissionArtifact.instructionPC 4164 = 5284 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4165 : Artifact.submissionArtifact.instructionPC 4165 = 5287 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4166 : Artifact.submissionArtifact.instructionPC 4166 = 5288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4167 : Artifact.submissionArtifact.instructionPC 4167 = 5289 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem stubPC4168 : Artifact.submissionArtifact.instructionPC 4168 = 5292 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

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

private theorem guard_stub_dest :
    Decode.isValidJumpDest submissionBytecode 5269 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4151 (by rfl)

private theorem guard_fallback_dest :
    Decode.isValidJumpDest submissionBytecode 360 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 199 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 98 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5035 []
private def byteEntry (input : ByteArray) (flag : UInt256) : State :=
  PatternedScan.stS input 5056 [flag]
private def byteDone (input : ByteArray) : State := PatternedScan.stS input 5068 []

private theorem run_guard_jump (input : ByteArray) :
    DirectGuard.run guardJumpPath (DirectGuard.guardEntry input) = some (sizeEntry input) := by
  rfl

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (byteEntry input (sizeFlag input)) := by
  let m : UInt256 := 4740813226943354766209
  let x : UInt256 := UInt256.ofNat input.size
  let d : UInt256 := x - 56
  let shifted : UInt256 := UInt256.shiftRight m d
  let bit : UInt256 := UInt256.land 1 shifted
  let l0 : Located := DirectGuard.opAt 4081 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4081 5035 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_jumpdest input 5035 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.pushAt 4082 10 4740813226943354766209
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4082 5036 [] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5036 10 4740813226943354766209 [] (by simp) (by decide) (by decide) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4083 1 56
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4083 5047 [m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5047 1 56 [m] (by simp) (by decide) (by decide) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4084 .CALLDATASIZE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4084 5049 [56, m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_calldatasize input 5049 [56, m] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4085 .SUB
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4085 5050 [x, 56, m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_sub input 5050 x 56 [m] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4086 .SHR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4086 5051 [d, m] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_shr input 5051 d m [] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.pushAt 4087 1 1
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4087 5052 [shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_push input 5052 1 1 [shifted] (by simp) (by decide) (by decide) (by norm_num))
  let l7 : Located := DirectGuard.opAt 4088 .AND
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4088 5054 [1, shifted] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_and input 5054 1 shifted [] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.opAt 4089 .ISZERO
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4089 5055 [bit] (by norm_num) (by
      rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide))
    (PatternedScan.stepS_iszero input 5055 bit [] (by simp) (by norm_num))
  have h01 := Stepper.runLocatedBlock_append [l0] [l1] _ _ _ h0 rfl h1
  have h02 := Stepper.runLocatedBlock_append [l0, l1] [l2] _ _ _ h01 rfl h2
  have h03 := Stepper.runLocatedBlock_append [l0, l1, l2] [l3] _ _ _ h02 rfl h3
  have h04 := Stepper.runLocatedBlock_append [l0, l1, l2, l3] [l4] _ _ _ h03 rfl h4
  have h05 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4] [l5] _ _ _ h04 rfl h5
  have h06 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5] [l6] _ _ _ h05 rfl h6
  have h07 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6] [l7] _ _ _ h06 rfl h7
  have h08 := Stepper.runLocatedBlock_append [l0, l1, l2, l3, l4, l5, l6, l7] [l8] _ _ _ h07 rfl h8
  have hf : UInt256.isZero bit = sizeFlag input := by
    have h := SizeLookupFlag.flag x
    rw [SizeLookupFlag.mask_literal] at h
    simpa only [bit, shifted, d, m, x, sizeFlag, Word.literal_eq_ofNat] using h
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
      some (PatternedScan.stS input 5067 [5269, byteFlag input flag]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let z := UInt256.xor 7 b
  let f := UInt256.lor z flag
  let l0 : Located := DirectGuard.pushAt 4090 0 0
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4090 5056 [flag] (by norm_num) entryPC4146)
    (PatternedScan.stepS_push0 input 5056 [flag] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4091 .CALLDATALOAD
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4091 5057 [0, flag] (by norm_num) entryPC4147)
    (PatternedScan.stepS_calldataload input 5057 0 [flag] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4092 0 0
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4092 5058 [w, flag] (by norm_num) entryPC4148)
    (PatternedScan.stepS_push0 input 5058 [w, flag] (by simp) (by norm_num))
  let l3 : Located := DirectGuard.opAt 4093 .BYTE
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4093 5059 [0, w, flag] (by norm_num) entryPC4149)
    (PatternedScan.stepS_byte input 5059 0 w [flag] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.pushAt 4094 1 7
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4094 5060 [b, flag] (by norm_num) entryPC4150)
    (PatternedScan.stepS_push input 5060 1 7 [b, flag] (by simp) (by decide) (by decide) (by norm_num))
  let l5 : Located := DirectGuard.opAt 4095 .XOR
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4095 5062 [7, b, flag] (by norm_num) entryPC4151)
    (PatternedScan.stepS_xor input 5062 7 b [flag] (by simp) (by norm_num))
  let l6 : Located := DirectGuard.opAt 4096 .OR
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4096 5063 [z, flag] (by norm_num) entryPC4152)
    (PatternedScan.stepS_or input 5063 z flag [] (by simp) (by norm_num))
  let l7 : Located := DirectGuard.pushAt 4097 2 5269
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4097 5064 [f] (by norm_num) entryPC4154)
    (PatternedScan.stepS_push input 5064 2 5269 [f] (by simp) (by decide) (by decide) (by norm_num))
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
      some (PatternedScan.stS input 5269 []) := by
  have ht := byteFlag_true input flag hflag
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4098 .JUMPI)
    (PatternedScan.pcFactS input 4098 5067 [5269, byteFlag input flag] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_taken input 5067 5269 5269 (byteFlag input flag) []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 5269)
      ht guard_stub_dest)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4098 .JUMPI] _ _ _ (run_guard_byte_prefix input flag) rfl hj

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) ∨
      DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (PatternedScan.stS input 5269 []) := by
  have hf : sizeFlag input = UInt256.ofNat 1 ∨
      (sizeFlag input = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7) := by
    by_cases hs : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128
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
      some (PatternedScan.stS input 5067 [5269, UInt256.ofNat 0]) := by
    simpa only [hf] using run_guard_byte_prefix input (UInt256.ofNat 0)
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4098 .JUMPI)
    (PatternedScan.pcFactS input 4098 5067 [5269, UInt256.ofNat 0] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_fall input 5067 5269 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4099 0 0)
    (PatternedScan.pcFactS input 4099 5068 [] (by norm_num) entryPC4156)
    (PatternedScan.stepS_push0 input 5068 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4100 1 98)
    (PatternedScan.pcFactS input 4100 5069 [0] (by norm_num) entryPC4157)
    (PatternedScan.stepS_push input 5069 1 98 [0] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4101 .JUMP)
    (PatternedScan.pcFactS input 4101 5071 [98, 0] (by norm_num) entryPC4158)
    (PatternedScan.stepS_jump input 5071 98 98 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 98) guard_match_dest)
  have hpj := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4098 .JUMPI] _ _ _ hprefix rfl hj
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4099 0 0] [DirectGuard.pushAt 4100 1 98] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4099 0 0, DirectGuard.pushAt 4100 1 98]
    [DirectGuard.opAt 4101 .JUMP] _ _ _ h01 rfl h2
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePath guardMatchSuffix _ _ _ hpj rfl hs

private theorem run_guard_match_helper (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128)
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

private theorem stubCond_false (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 32 ∨ DirectGuard.firstByte input ≠ 7) :
    ¬ UInt256.isTrue
        (((UInt256.ofNat 7).xor
            ((UInt256.ofNat 0).byteAt (MachineState.readWord input 0))).isZero.land
          ((UInt256.ofNat 32).eq (UInt256.ofNat input.size))) := by
  rcases hne with hs | hb
  · have heq := DirectGuard.size_eq_zero input 32
      (Nat.lt_trans hfit (by norm_num)) (by norm_num) hs
    rw [heq]
    intro htrue
    have hz :
        (((UInt256.ofNat 7).xor
            ((UInt256.ofNat 0).byteAt (MachineState.readWord input 0))).isZero.land
          (0 : UInt256)).toNat = 0 := by
      rw [Challenge.EvmProof.Word.word_toNat_land]
      exact Nat.and_zero _
    exact htrue hz
  · rw [firstByte_eq_byteAt]
    have hx :
        (UInt256.ofNat 7).xor (UInt256.ofNat (DirectGuard.firstByte input)) ≠ 0 := by
      intro h0
      have heq := (KnownInputLogic.wordXor_eq_zero_iff _ _).mp h0
      have hlt : DirectGuard.firstByte input < 2 ^ 256 := by
        unfold DirectGuard.firstByte
        exact Nat.lt_trans (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt (by norm_num)
      have hn := congrArg UInt256.toNat heq
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num), Nat.mod_eq_of_lt hlt] at hn
      exact hb hn.symm
    have hz :
        ((UInt256.ofNat 7).xor (UInt256.ofNat (DirectGuard.firstByte input))).isZero = 0 := by
      unfold UInt256.isZero
      split_ifs with hto
      · exact False.elim (hx (Challenge.EvmProof.Word.word_ext hto))
      · rfl
    rw [hz]
    intro htrue
    have hz :
        ((0 : UInt256).land ((UInt256.ofNat 32).eq (UInt256.ofNat input.size))).toNat = 0 := by
      rw [Challenge.EvmProof.Word.word_toNat_land]
      exact Nat.zero_and _
    exact htrue hz

private theorem run_stub_fail (input : ByteArray) (hfit : CalldataFits input)
    (hne : input.size ≠ 32 ∨ DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run stubFailPath (PatternedScan.stS input 5269 []) =
      some (DirectGuard.fallbackState input) := by
  have hfalse : ¬ (UInt256.ofNat 0).isTrue := by decide
  have hf := stubCond_false input hfit hne
  simp (config := { maxSteps := 400000 })
    [stubFailPath, stubPath, stubFailTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     PatternedScan.stS, DirectGuard.fallbackState, DirectGuard.atPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     stubPC4151, stubPC4152, stubPC4153, stubPC4154, stubPC4155, stubPC4156,
     stubPC4157, stubPC4158, stubPC4159, stubPC4160, stubPC4161, stubPC4162,
     stubPC4163, stubPC4164, stubPC4165, stubPC4166, stubPC4167, stubPC4168,
     guard_match_dest, guard_fallback_dest, hfalse, hf, if_neg hf]


private theorem stubCond_true (input : ByteArray)
    (hsize : input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
    UInt256.isTrue
        (((UInt256.ofNat 7).xor
            ((UInt256.ofNat 0).byteAt (MachineState.readWord input 0))).isZero.land
          ((UInt256.ofNat 32).eq (UInt256.ofNat input.size))) := by
  rw [firstByte_eq_byteAt, hbyte, hsize]
  decide

private theorem run_stub_hit32 (input : ByteArray)
    (hsize : input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run stubPath (PatternedScan.stS input 5269 []) =
      some (guardJumpState input) := by
  simp (config := { maxSteps := 400000 })
    [stubPath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     PatternedScan.stS, DirectGuard.atPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.literal_eq_ofNat,
     Challenge.EvmProof.Word.succ_ofNat_mod,
     Challenge.EvmProof.Word.ofNat_add_mod,
     Challenge.EvmProof.Word.word_toNat_ofNat,
     stubPC4151, stubPC4152, stubPC4153, stubPC4154, stubPC4155, stubPC4156,
     stubPC4157, stubPC4158, stubPC4159, stubPC4160, stubPC4161, stubPC4162,
     stubPC4163, stubPC4164, stubPC4165, guard_match_dest]
  have ht := stubCond_true input hsize hbyte
  rw [if_pos ht]
  simp [guardJumpState, DirectGuard.guardEntry, DirectGuard.atPC, PatternedScan.stS]

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) ∨
      DirectGuard.firstByte input ≠ 7)
    (hne32 : input.size ≠ 32 ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  (sound guardCheckPath (run_guard_fail input hfit hbad)).trans
    (sound stubFailPath (run_stub_fail input hfit hne32))

def gasSteps_hit32 (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  have hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧
      input.size ≠ 65 ∧ input.size ≠ 128) ∨ DirectGuard.firstByte input ≠ 7 :=
    Or.inl ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      ((sound guardCheckPath (run_guard_fail input hfit hbad)).trans
        ((sound stubPath (run_stub_hit32 input hsize hbyte)).trans
          (sound guardMatchTail (run_guard_match_tail input)))))

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match_helper input hfit hsize hbyte)).trans
    (sound guardMatchTail (run_guard_match_tail input))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128) ∨
      DirectGuard.firstByte input ≠ 7)
    (hne32 : input.size ≠ 32 ∨ DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad hne32))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
