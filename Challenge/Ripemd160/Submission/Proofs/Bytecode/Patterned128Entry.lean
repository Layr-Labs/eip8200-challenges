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
@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 61 = 101 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 62 = 102 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4142 : Artifact.submissionArtifact.instructionPC 4142 = 5132 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4143 : Artifact.submissionArtifact.instructionPC 4143 = 5133 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4144 : Artifact.submissionArtifact.instructionPC 4144 = 5136 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4145 : Artifact.submissionArtifact.instructionPC 4145 = 5137 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4146 : Artifact.submissionArtifact.instructionPC 4146 = 5138 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4147 : Artifact.submissionArtifact.instructionPC 4147 = 5139 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4148 : Artifact.submissionArtifact.instructionPC 4148 = 5140 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4149 : Artifact.submissionArtifact.instructionPC 4149 = 5141 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4150 : Artifact.submissionArtifact.instructionPC 4150 = 5142 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4151 : Artifact.submissionArtifact.instructionPC 4151 = 5144 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4152 : Artifact.submissionArtifact.instructionPC 4152 = 5145 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4153 : Artifact.submissionArtifact.instructionPC 4153 = 5146 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4154 : Artifact.submissionArtifact.instructionPC 4154 = 5147 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4155 : Artifact.submissionArtifact.instructionPC 4155 = 5150 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4156 : Artifact.submissionArtifact.instructionPC 4156 = 5151 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4157 : Artifact.submissionArtifact.instructionPC 4157 = 5152 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4158 : Artifact.submissionArtifact.instructionPC 4158 = 5154 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4166 : Artifact.submissionArtifact.instructionPC 4166 = 5182 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4167 : Artifact.submissionArtifact.instructionPC 4167 = 5183 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4168 : Artifact.submissionArtifact.instructionPC 4168 = 5184 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4169 : Artifact.submissionArtifact.instructionPC 4169 = 5186 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4170 : Artifact.submissionArtifact.instructionPC 4170 = 5187 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4171 : Artifact.submissionArtifact.instructionPC 4171 = 5188 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4172 : Artifact.submissionArtifact.instructionPC 4172 = 5190 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4173 : Artifact.submissionArtifact.instructionPC 4173 = 5191 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4174 : Artifact.submissionArtifact.instructionPC 4174 = 5192 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4175 : Artifact.submissionArtifact.instructionPC 4175 = 5193 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4176 : Artifact.submissionArtifact.instructionPC 4176 = 5195 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4177 : Artifact.submissionArtifact.instructionPC 4177 = 5196 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4178 : Artifact.submissionArtifact.instructionPC 4178 = 5197 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4179 : Artifact.submissionArtifact.instructionPC 4179 = 5198 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC4180 : Artifact.submissionArtifact.instructionPC 4180 = 5201 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryOr00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by rfl

@[simp] private theorem entryOr01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) = UInt256.ofNat 1 := by rfl

@[simp] private theorem entryOr11 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 1) = UInt256.ofNat 1 := by rfl

private def guardJumpPath : List Located :=
  [DirectGuard.opAt 4142 .JUMPDEST,
   DirectGuard.pushAt 4143 2 5182,
   DirectGuard.opAt 4144 .JUMP]

private def guardSizePath : List Located :=
  [DirectGuard.opAt 4166 .JUMPDEST,
   DirectGuard.opAt 4167 .CALLDATASIZE,
   DirectGuard.pushAt 4168 1 56,
   DirectGuard.opAt 4169 .EQ,
   DirectGuard.opAt 4170 .CALLDATASIZE,
   DirectGuard.pushAt 4171 1 120,
   DirectGuard.opAt 4172 .EQ,
   DirectGuard.opAt 4173 .OR,
   DirectGuard.opAt 4174 .CALLDATASIZE,
   DirectGuard.pushAt 4175 1 128,
   DirectGuard.opAt 4176 .EQ,
   DirectGuard.opAt 4177 .OR,
   DirectGuard.opAt 4178 .ISZERO,
   DirectGuard.pushAt 4179 2 5137,
   DirectGuard.opAt 4180 .JUMP]

private def guardBytePrefix : List Located :=
  [DirectGuard.opAt 4145 .JUMPDEST,
   DirectGuard.pushAt 4146 0 0,
   DirectGuard.opAt 4147 .CALLDATALOAD,
   DirectGuard.pushAt 4148 0 0,
   DirectGuard.opAt 4149 .BYTE,
   DirectGuard.pushAt 4150 1 7,
   DirectGuard.opAt 4151 .EQ,
   DirectGuard.opAt 4152 .ISZERO,
   DirectGuard.opAt 4153 .OR,
   DirectGuard.pushAt 4154 2 368]

private def guardBytePath : List Located := guardBytePrefix ++ [DirectGuard.opAt 4155 .JUMPI]

private def guardCheckPath : List Located := guardJumpPath ++ guardSizePath ++ guardBytePath

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4156 0 0,
   DirectGuard.pushAt 4157 1 101,
   DirectGuard.opAt 4158 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 61 .JUMPDEST, DirectGuard.opAt 62 .POP]

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
  Artifact.submissionArtifact.isValidJumpDest_index 205 (by rfl)

private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 101 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 61 (by rfl)

private theorem guard_size_dest :
    Decode.isValidJumpDest submissionBytecode 5182 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4166 (by rfl)

private theorem guard_byte_dest :
    Decode.isValidJumpDest submissionBytecode 5137 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 4145 (by rfl)

private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 5182 []
private def byteEntry (input : ByteArray) (flag : UInt256) : State :=
  PatternedScan.stS input 5137 [flag]
private def byteDone (input : ByteArray) : State := PatternedScan.stS input 5151 []

private theorem run_guard_jump (input : ByteArray) :
    DirectGuard.run guardJumpPath (DirectGuard.guardEntry input) = some (sizeEntry input) := by
  have h0 := PatternedScan.blockOfS (DirectGuard.opAt 4142 .JUMPDEST)
    (PatternedScan.pcFactS input 4142 5132 [] (by norm_num) entryPC4142)
    (PatternedScan.stepS_jumpdest input 5132 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4143 2 5182)
    (PatternedScan.pcFactS input 4143 5133 [] (by norm_num) entryPC4143)
    (PatternedScan.stepS_push input 5133 2 5182 [] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4144 .JUMP)
    (PatternedScan.pcFactS input 4144 5136 [5182] (by norm_num) entryPC4144)
    (PatternedScan.stepS_jump input 5136 5182 5182 [] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 5182) guard_size_dest)
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4142 .JUMPDEST] [DirectGuard.pushAt 4143 2 5182] _ _ _ h0 rfl h1
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4142 .JUMPDEST, DirectGuard.pushAt 4143 2 5182]
    [DirectGuard.opAt 4144 .JUMP] _ _ _ h01 rfl h2

private theorem run_guard_size (input : ByteArray) :
    DirectGuard.run guardSizePath (sizeEntry input) = some (byteEntry input (sizeFlag input)) := by
  let l0 : Located := DirectGuard.opAt 4166 .JUMPDEST
  have h0 := PatternedScan.blockOfS l0
    (PatternedScan.pcFactS input 4166 5182 [] (by norm_num) entryPC4166)
    (PatternedScan.stepS_jumpdest input 5182 [] (by simp) (by norm_num))
  let l1 : Located := DirectGuard.opAt 4167 .CALLDATASIZE
  have h1 := PatternedScan.blockOfS l1
    (PatternedScan.pcFactS input 4167 5183 [] (by norm_num) entryPC4167)
    (PatternedScan.stepS_calldatasize input 5183 [] (by simp) (by norm_num))
  let l2 : Located := DirectGuard.pushAt 4168 1 56
  have h2 := PatternedScan.blockOfS l2
    (PatternedScan.pcFactS input 4168 5184 [(UInt256.ofNat input.size)] (by norm_num) entryPC4168)
    (PatternedScan.stepS_push input 5184 1 56 [(UInt256.ofNat input.size)] (by simp) (by decide) (by decide) (by norm_num))
  let v3 : UInt256 := UInt256.eq (56 : UInt256) (UInt256.ofNat input.size)
  let l3 : Located := DirectGuard.opAt 4169 .EQ
  have h3 := PatternedScan.blockOfS l3
    (PatternedScan.pcFactS input 4169 5186 [(56 : UInt256), (UInt256.ofNat input.size)] (by norm_num) entryPC4169)
    (PatternedScan.stepS_eq input 5186 (56 : UInt256) (UInt256.ofNat input.size) [] (by simp) (by norm_num))
  let l4 : Located := DirectGuard.opAt 4170 .CALLDATASIZE
  have h4 := PatternedScan.blockOfS l4
    (PatternedScan.pcFactS input 4170 5187 [v3] (by norm_num) entryPC4170)
    (PatternedScan.stepS_calldatasize input 5187 [v3] (by simp) (by norm_num))
  let l5 : Located := DirectGuard.pushAt 4171 1 120
  have h5 := PatternedScan.blockOfS l5
    (PatternedScan.pcFactS input 4171 5188 [(UInt256.ofNat input.size), v3] (by norm_num) entryPC4171)
    (PatternedScan.stepS_push input 5188 1 120 [(UInt256.ofNat input.size), v3] (by simp) (by decide) (by decide) (by norm_num))
  let v6 : UInt256 := UInt256.eq (120 : UInt256) (UInt256.ofNat input.size)
  let l6 : Located := DirectGuard.opAt 4172 .EQ
  have h6 := PatternedScan.blockOfS l6
    (PatternedScan.pcFactS input 4172 5190 [(120 : UInt256), (UInt256.ofNat input.size), v3] (by norm_num) entryPC4172)
    (PatternedScan.stepS_eq input 5190 (120 : UInt256) (UInt256.ofNat input.size) [v3] (by simp) (by norm_num))
  let v7 : UInt256 := UInt256.lor v6 v3
  let l7 : Located := DirectGuard.opAt 4173 .OR
  have h7 := PatternedScan.blockOfS l7
    (PatternedScan.pcFactS input 4173 5191 [v6, v3] (by norm_num) entryPC4173)
    (PatternedScan.stepS_or input 5191 v6 v3 [] (by simp) (by norm_num))
  let l8 : Located := DirectGuard.opAt 4174 .CALLDATASIZE
  have h8 := PatternedScan.blockOfS l8
    (PatternedScan.pcFactS input 4174 5192 [v7] (by norm_num) entryPC4174)
    (PatternedScan.stepS_calldatasize input 5192 [v7] (by simp) (by norm_num))
  let l9 : Located := DirectGuard.pushAt 4175 1 128
  have h9 := PatternedScan.blockOfS l9
    (PatternedScan.pcFactS input 4175 5193 [(UInt256.ofNat input.size), v7] (by norm_num) entryPC4175)
    (PatternedScan.stepS_push input 5193 1 128 [(UInt256.ofNat input.size), v7] (by simp) (by decide) (by decide) (by norm_num))
  let v10 : UInt256 := UInt256.eq (128 : UInt256) (UInt256.ofNat input.size)
  let l10 : Located := DirectGuard.opAt 4176 .EQ
  have h10 := PatternedScan.blockOfS l10
    (PatternedScan.pcFactS input 4176 5195 [(128 : UInt256), (UInt256.ofNat input.size), v7] (by norm_num) entryPC4176)
    (PatternedScan.stepS_eq input 5195 (128 : UInt256) (UInt256.ofNat input.size) [v7] (by simp) (by norm_num))
  let v11 : UInt256 := UInt256.lor v10 v7
  let l11 : Located := DirectGuard.opAt 4177 .OR
  have h11 := PatternedScan.blockOfS l11
    (PatternedScan.pcFactS input 4177 5196 [v10, v7] (by norm_num) entryPC4177)
    (PatternedScan.stepS_or input 5196 v10 v7 [] (by simp) (by norm_num))
  let v12 : UInt256 := UInt256.isZero v11
  let l12 : Located := DirectGuard.opAt 4178 .ISZERO
  have h12 := PatternedScan.blockOfS l12
    (PatternedScan.pcFactS input 4178 5197 [v11] (by norm_num) entryPC4178)
    (PatternedScan.stepS_iszero input 5197 v11 [] (by simp) (by norm_num))
  let l13 : Located := DirectGuard.pushAt 4179 2 5137
  have h13 := PatternedScan.blockOfS l13
    (PatternedScan.pcFactS input 4179 5198 [v12] (by norm_num) entryPC4179)
    (PatternedScan.stepS_push input 5198 2 5137 [v12] (by simp) (by decide) (by decide) (by norm_num))
  let l14 : Located := DirectGuard.opAt 4180 .JUMP
  have h14 := PatternedScan.blockOfS l14
    (PatternedScan.pcFactS input 4180 5201 [(5137 : UInt256), v12] (by norm_num) entryPC4180)
    (PatternedScan.stepS_jump input 5201 5137 (5137 : UInt256) [v12] (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 5137) guard_byte_dest)
  have h1_3 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l1] [l2] _ _ _ h1 rfl h2
  have h0_3 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l0] [l1, l2] _ _ _ h0 rfl h1_3
  have h3_5 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l3] [l4] _ _ _ h3 rfl h4
  have h5_7 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l5] [l6] _ _ _ h5 rfl h6
  have h3_7 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l3, l4] [l5, l6] _ _ _ h3_5 rfl h5_7
  have h0_7 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l0, l1, l2] [l3, l4, l5, l6] _ _ _ h0_3 rfl h3_7
  have h7_9 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l7] [l8] _ _ _ h7 rfl h8
  have h9_11 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l9] [l10] _ _ _ h9 rfl h10
  have h7_11 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l7, l8] [l9, l10] _ _ _ h7_9 rfl h9_11
  have h11_13 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l11] [l12] _ _ _ h11 rfl h12
  have h13_15 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l13] [l14] _ _ _ h13 rfl h14
  have h11_15 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l11, l12] [l13, l14] _ _ _ h11_13 rfl h13_15
  have h7_15 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l7, l8, l9, l10] [l11, l12, l13, l14] _ _ _ h7_11 rfl h11_15
  have h0_15 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [l0, l1, l2, l3, l4, l5, l6] [l7, l8, l9, l10, l11, l12, l13, l14] _ _ _ h0_7 rfl h7_15
  have hv : v12 = sizeFlag input := by
    simp only [sizeFlag, v3, v6, v7, v10, v11, v12, Challenge.EvmProof.Word.literal_eq_ofNat]
  rw [hv] at h0_15
  exact h0_15


private def byteFlag (input : ByteArray) (flag : UInt256) : UInt256 :=
  UInt256.lor (UInt256.isZero (UInt256.eq (UInt256.ofNat 7)
    (UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0)))) flag

private theorem byteFlag_one (input : ByteArray) (flag : UInt256)
    (hflag : flag = UInt256.ofNat 1 ∨
      (flag = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7)) :
    byteFlag input flag = UInt256.ofNat 1 := by
  unfold byteFlag
  rcases hflag with hflag | ⟨hflag, hbyte⟩
  · rw [hflag]
    by_cases hbyte : DirectGuard.firstByte input = 7
    · rw [guard_byte_eq_one input hbyte]
      decide
    · rw [guard_byte_eq_zero input hbyte]
      decide
  · rw [hflag, guard_byte_eq_zero input hbyte]
    decide

private theorem byteFlag_zero (input : ByteArray) (hbyte : DirectGuard.firstByte input = 7) :
    byteFlag input (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  unfold byteFlag
  rw [guard_byte_eq_one input hbyte]
  decide

private theorem run_guard_byte_prefix (input : ByteArray) (flag : UInt256) :
    DirectGuard.run guardBytePrefix (byteEntry input flag) =
      some (PatternedScan.stS input 5150 [368, byteFlag input flag]) := by
  let w := MachineState.readWord input 0
  let b := UInt256.byteAt 0 w
  let e := UInt256.eq 7 b
  let z := UInt256.isZero e
  let f := UInt256.lor z flag
  have h0 := PatternedScan.blockOfS (DirectGuard.opAt 4145 .JUMPDEST)
    (PatternedScan.pcFactS input 4145 5137 [flag] (by norm_num) entryPC4145)
    (PatternedScan.stepS_jumpdest input 5137 [flag] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4146 0 0)
    (PatternedScan.pcFactS input 4146 5138 [flag] (by norm_num) entryPC4146)
    (PatternedScan.stepS_push0 input 5138 [flag] (by simp) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4147 .CALLDATALOAD)
    (PatternedScan.pcFactS input 4147 5139 [0, flag] (by norm_num) entryPC4147)
    (PatternedScan.stepS_calldataload input 5139 0 [flag] (by simp) (by norm_num))
  have h3 := PatternedScan.blockOfS (DirectGuard.pushAt 4148 0 0)
    (PatternedScan.pcFactS input 4148 5140 [w, flag] (by norm_num) entryPC4148)
    (PatternedScan.stepS_push0 input 5140 [w, flag] (by simp) (by norm_num))
  have h4 := PatternedScan.blockOfS (DirectGuard.opAt 4149 .BYTE)
    (PatternedScan.pcFactS input 4149 5141 [0, w, flag] (by norm_num) entryPC4149)
    (PatternedScan.stepS_byte input 5141 0 w [flag] (by simp) (by norm_num))
  have h5 := PatternedScan.blockOfS (DirectGuard.pushAt 4150 1 7)
    (PatternedScan.pcFactS input 4150 5142 [b, flag] (by norm_num) entryPC4150)
    (PatternedScan.stepS_push input 5142 1 7 [b, flag] (by simp) (by decide) (by decide) (by norm_num))
  have h6 := PatternedScan.blockOfS (DirectGuard.opAt 4151 .EQ)
    (PatternedScan.pcFactS input 4151 5144 [7, b, flag] (by norm_num) entryPC4151)
    (PatternedScan.stepS_eq input 5144 7 b [flag] (by simp) (by norm_num))
  have h7 := PatternedScan.blockOfS (DirectGuard.opAt 4152 .ISZERO)
    (PatternedScan.pcFactS input 4152 5145 [e, flag] (by norm_num) entryPC4152)
    (PatternedScan.stepS_iszero input 5145 e [flag] (by simp) (by norm_num))
  have h8 := PatternedScan.blockOfS (DirectGuard.opAt 4153 .OR)
    (PatternedScan.pcFactS input 4153 5146 [z, flag] (by norm_num) entryPC4153)
    (PatternedScan.stepS_or input 5146 z flag [] (by simp) (by norm_num))
  have h9 := PatternedScan.blockOfS (DirectGuard.pushAt 4154 2 368)
    (PatternedScan.pcFactS input 4154 5147 [f] (by norm_num) entryPC4154)
    (PatternedScan.stepS_push input 5147 2 368 [f] (by simp) (by decide) (by decide) (by norm_num))
  have a1 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST] [DirectGuard.pushAt 4146 0 0] _ _ _ h0 rfl h1
  have a2 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0] [DirectGuard.opAt 4147 .CALLDATALOAD] _ _ _ a1 rfl h2
  have a3 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD] [DirectGuard.pushAt 4148 0 0] _ _ _ a2 rfl h3
  have a4 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD, DirectGuard.pushAt 4148 0 0] [DirectGuard.opAt 4149 .BYTE] _ _ _ a3 rfl h4
  have a5 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD, DirectGuard.pushAt 4148 0 0, DirectGuard.opAt 4149 .BYTE] [DirectGuard.pushAt 4150 1 7] _ _ _ a4 rfl h5
  have a6 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD, DirectGuard.pushAt 4148 0 0, DirectGuard.opAt 4149 .BYTE, DirectGuard.pushAt 4150 1 7] [DirectGuard.opAt 4151 .EQ] _ _ _ a5 rfl h6
  have a7 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD, DirectGuard.pushAt 4148 0 0, DirectGuard.opAt 4149 .BYTE, DirectGuard.pushAt 4150 1 7, DirectGuard.opAt 4151 .EQ] [DirectGuard.opAt 4152 .ISZERO] _ _ _ a6 rfl h7
  have a8 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD, DirectGuard.pushAt 4148 0 0, DirectGuard.opAt 4149 .BYTE, DirectGuard.pushAt 4150 1 7, DirectGuard.opAt 4151 .EQ, DirectGuard.opAt 4152 .ISZERO] [DirectGuard.opAt 4153 .OR] _ _ _ a7 rfl h8
  have a9 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.opAt 4145 .JUMPDEST, DirectGuard.pushAt 4146 0 0, DirectGuard.opAt 4147 .CALLDATALOAD, DirectGuard.pushAt 4148 0 0, DirectGuard.opAt 4149 .BYTE, DirectGuard.pushAt 4150 1 7, DirectGuard.opAt 4151 .EQ, DirectGuard.opAt 4152 .ISZERO, DirectGuard.opAt 4153 .OR] [DirectGuard.pushAt 4154 2 368] _ _ _ a8 rfl h9
  have hf : f = byteFlag input flag := by
    simp only [f, z, e, b, w, byteFlag, Challenge.EvmProof.Word.literal_eq_ofNat]
  rw [hf] at a9
  exact a9

private theorem run_guard_byte_fail (input : ByteArray) (flag : UInt256)
    (hflag : flag = UInt256.ofNat 1 ∨
      (flag = UInt256.ofNat 0 ∧ DirectGuard.firstByte input ≠ 7)) :
    DirectGuard.run guardBytePath (byteEntry input flag) = some (DirectGuard.fallbackState input) := by
  have hf := byteFlag_one input flag hflag
  have ht : UInt256.isTrue (byteFlag input flag) := by rw [hf]; decide
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4155 .JUMPI)
    (PatternedScan.pcFactS input 4155 5150 [368, byteFlag input flag] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_taken input 5150 368 368 (byteFlag input flag) []
      (by simp) (by norm_num) (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 368)
      ht guard_fallback_dest)
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4155 .JUMPI] _ _ _ (run_guard_byte_prefix input flag) rfl hj

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
      some (PatternedScan.stS input 5150 [368, UInt256.ofNat 0]) := by
    simpa only [hf] using run_guard_byte_prefix input (UInt256.ofNat 0)
  have hj := PatternedScan.blockOfS (DirectGuard.opAt 4155 .JUMPI)
    (PatternedScan.pcFactS input 4155 5150 [368, UInt256.ofNat 0] (by norm_num) entryPC4155)
    (PatternedScan.stepS_jumpi_fall input 5150 368 (UInt256.ofNat 0) []
      (by simp) (by norm_num) (by decide))
  have h0 := PatternedScan.blockOfS (DirectGuard.pushAt 4156 0 0)
    (PatternedScan.pcFactS input 4156 5151 [] (by norm_num) entryPC4156)
    (PatternedScan.stepS_push0 input 5151 [] (by simp) (by norm_num))
  have h1 := PatternedScan.blockOfS (DirectGuard.pushAt 4157 1 101)
    (PatternedScan.pcFactS input 4157 5152 [0] (by norm_num) entryPC4157)
    (PatternedScan.stepS_push input 5152 1 101 [0] (by simp) (by decide) (by decide) (by norm_num))
  have h2 := PatternedScan.blockOfS (DirectGuard.opAt 4158 .JUMP)
    (PatternedScan.pcFactS input 4158 5154 [101, 0] (by norm_num) entryPC4158)
    (PatternedScan.stepS_jump input 5154 101 101 [0] (by simp) (by norm_num)
      (by simpa using Challenge.EvmProof.Word.literal_eq_ofNat 101) guard_match_dest)
  have hpj := Challenge.EvmProof.Stepper.runLocatedBlock_append
    guardBytePrefix [DirectGuard.opAt 4155 .JUMPI] _ _ _ hprefix rfl hj
  have h01 := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4156 0 0] [DirectGuard.pushAt 4157 1 101] _ _ _ h0 rfl h1
  have hs := Challenge.EvmProof.Stepper.runLocatedBlock_append
    [DirectGuard.pushAt 4156 0 0, DirectGuard.pushAt 4157 1 101]
    [DirectGuard.opAt 4158 .JUMP] _ _ _ h01 rfl h2
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
