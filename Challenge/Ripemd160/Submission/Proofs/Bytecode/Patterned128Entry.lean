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

/-! The appended eight-size guard and its bridge into the patterned scan. -/

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
    Decode.isValidJumpDest submissionBytecode 276 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 179 (by rfl)
private theorem guard_match_dest :
    Decode.isValidJumpDest submissionBytecode 98 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)
@[simp] private theorem pc5038 : Artifact.submissionArtifact.instructionPC 4061 = 4951 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5039 : Artifact.submissionArtifact.instructionPC 4062 = 4952 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5050 : Artifact.submissionArtifact.instructionPC 4063 = 4963 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5052 : Artifact.submissionArtifact.instructionPC 4064 = 4965 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5053 : Artifact.submissionArtifact.instructionPC 4065 = 4966 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5054 : Artifact.submissionArtifact.instructionPC 4066 = 4967 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5055 : Artifact.submissionArtifact.instructionPC 4067 = 4968 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5056 : Artifact.submissionArtifact.instructionPC 4068 = 4969 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5057 : Artifact.submissionArtifact.instructionPC 4069 = 4970 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5058 : Artifact.submissionArtifact.instructionPC 4070 = 4971 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5059 : Artifact.submissionArtifact.instructionPC 4071 = 4972 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5061 : Artifact.submissionArtifact.instructionPC 4072 = 4974 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5062 : Artifact.submissionArtifact.instructionPC 4073 = 4975 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5063 : Artifact.submissionArtifact.instructionPC 4074 = 4976 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5064 : Artifact.submissionArtifact.instructionPC 4075 = 4977 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5067 : Artifact.submissionArtifact.instructionPC 4076 = 4980 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5068 : Artifact.submissionArtifact.instructionPC 4077 = 4981 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5069 : Artifact.submissionArtifact.instructionPC 4078 = 4982 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc5071 : Artifact.submissionArtifact.instructionPC 4079 = 4984 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc98 : Artifact.submissionArtifact.instructionPC 59 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc99 : Artifact.submissionArtifact.instructionPC 60 = 99 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide

private def prefixPath : List Located :=
  [DirectGuard.opAt 4061 .JUMPDEST,
   DirectGuard.pushAt 4062 10 9500073197960419084035,
   DirectGuard.pushAt 4063 1 55,
   DirectGuard.opAt 4064 .CALLDATASIZE,
   DirectGuard.opAt 4065 .SUB,
   DirectGuard.opAt 4066 .SHR,
   DirectGuard.pushAt 4067 0 0,
   DirectGuard.opAt 4068 .CALLDATALOAD,
   DirectGuard.pushAt 4069 0 0,
   DirectGuard.opAt 4070 .BYTE,
   DirectGuard.pushAt 4071 1 7,
   DirectGuard.opAt 4072 .EQ,
   DirectGuard.opAt 4073 .AND,
   DirectGuard.opAt 4074 .ISZERO,
   DirectGuard.pushAt 4075 2 276]
private def jumpPath : List Located := [DirectGuard.opAt 4076 .JUMPI]
private def matchPath : List Located :=
  [DirectGuard.pushAt 4077 0 0,
   DirectGuard.pushAt 4078 1 98,
   DirectGuard.opAt 4079 .JUMP,
   DirectGuard.opAt 59 .JUMPDEST,
   DirectGuard.opAt 60 .POP]
private def shifted (input : ByteArray) : UInt256 :=
  UInt256.shiftRight 9500073197960419084035 (UInt256.ofNat input.size - 55)
private def flag (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.land
    (UInt256.eq 7 (UInt256.byteAt 0 (MachineState.readWord input 0))) (shifted input))
private def jumpState (input : ByteArray) : State :=
  PatternedScan.stS input 4980 [276, flag input]

private theorem run_prefix (input : ByteArray) :
    DirectGuard.run prefixPath (DirectGuard.guardEntry input) = some (jumpState input) := by
  simp [prefixPath, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.run, DirectGuard.guardEntry, DirectGuard.atPC,
    jumpState, PatternedScan.stS, PatternedScan.atPC, shifted, flag,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

private theorem flag_match (input : ByteArray)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55) (hbyte : DirectGuard.firstByte input = 7) :
    flag input = 0 := by
  unfold flag
  rw [show UInt256.eq 7 (UInt256.byteAt 0 (MachineState.readWord input 0)) = 1 from guard_byte_eq_one input hbyte]
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  have hf : UInt256.isZero (UInt256.land 1 (shifted input)) = sizeFlag input := h
  rw [hf, sizeFlag_hit input hsize]
  rfl

private theorem flag_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55) ∨ DirectGuard.firstByte input ≠ 7) :
    flag input = 1 := by
  by_cases hb : DirectGuard.firstByte input = 7
  · have hs : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 := by tauto
    unfold flag
    rw [show UInt256.eq 7 (UInt256.byteAt 0 (MachineState.readWord input 0)) = 1 from guard_byte_eq_one input hb]
    have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
    rw [SizeLookupFlag.mask_literal] at h
    have hf : UInt256.isZero (UInt256.land 1 (shifted input)) = sizeFlag input := h
    rw [hf, sizeFlag_fail input hfit hs]
    rfl
  · unfold flag
    rw [show UInt256.eq 7 (UInt256.byteAt 0 (MachineState.readWord input 0)) = 0 from guard_byte_eq_zero input hb]
    have hz : UInt256.land 0 (shifted input) = 0 := by
      apply Word.word_ext
      rw [Word.word_toNat_land]
      simp [Word.word_toNat_ofNat]
    rw [hz]
    decide

private theorem run_fail (input : ByteArray) (h : flag input = 1) :
    DirectGuard.run jumpPath (jumpState input) = some (DirectGuard.fallbackState input) := by
  simp [jumpPath, jumpState, h, DirectGuard.run, DirectGuard.opAt,
    PatternedScan.stS, PatternedScan.atPC, DirectGuard.fallbackState, DirectGuard.atPC,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    UInt256.isTrue, guard_fallback_dest, Word.literal_eq_ofNat, Word.word_toNat_ofNat]

private theorem run_match (input : ByteArray) (h : flag input = 0) :
    DirectGuard.run (jumpPath ++ matchPath) (jumpState input) =
      some (PatternedScan.patternedEntry input) := by
  simp [jumpPath, matchPath, jumpState, h, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    UInt256.isTrue, guard_match_dest, Word.literal_eq_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55) ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  (sound prefixPath (run_prefix input)).trans
    (sound jumpPath (run_fail input (flag_fail input hfit hbad)))

def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound prefixPath (run_prefix input)).trans
    (sound (jumpPath ++ matchPath) (run_match input (flag_match input hsize hbyte)))
def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55) (hbyte : DirectGuard.firstByte input = 7) :
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55) ∨
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
