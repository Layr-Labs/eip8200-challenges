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

/-! The early-byte guard for eleven fully checked input sizes and its bridge into the patterned scan. -/

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

@[simp] private theorem entryPC61 : Artifact.submissionArtifact.instructionPC 59 = 98 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]
  decide

@[simp] private theorem entryPC62 : Artifact.submissionArtifact.instructionPC 60 = 99 := by
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

private theorem guard_fallback_dest : Decode.isValidJumpDest submissionBytecode 393 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 255 (by rfl)
private theorem guard_match_dest : Decode.isValidJumpDest submissionBytecode 98 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 59 (by rfl)
@[simp] private theorem pc4799 : Artifact.submissionArtifact.instructionPC 179 = 276 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4800 : Artifact.submissionArtifact.instructionPC 180 = 277 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4801 : Artifact.submissionArtifact.instructionPC 181 = 278 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4802 : Artifact.submissionArtifact.instructionPC 182 = 279 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4803 : Artifact.submissionArtifact.instructionPC 183 = 280 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4804 : Artifact.submissionArtifact.instructionPC 184 = 281 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4806 : Artifact.submissionArtifact.instructionPC 185 = 283 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4807 : Artifact.submissionArtifact.instructionPC 186 = 284 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4810 : Artifact.submissionArtifact.instructionPC 187 = 287 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4811 : Artifact.submissionArtifact.instructionPC 188 = 288 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4829 : Artifact.submissionArtifact.instructionPC 189 = 306 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4830 : Artifact.submissionArtifact.instructionPC 190 = 307 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4831 : Artifact.submissionArtifact.instructionPC 191 = 308 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4833 : Artifact.submissionArtifact.instructionPC 192 = 310 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4834 : Artifact.submissionArtifact.instructionPC 193 = 311 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4835 : Artifact.submissionArtifact.instructionPC 194 = 312 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4838 : Artifact.submissionArtifact.instructionPC 195 = 315 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4839 : Artifact.submissionArtifact.instructionPC 196 = 316 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4840 : Artifact.submissionArtifact.instructionPC 197 = 317 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
@[simp] private theorem pc4842 : Artifact.submissionArtifact.instructionPC 198 = 319 := by
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide
private def bytePrefix : List Located :=
  [ DirectGuard.opAt 179 .JUMPDEST,
    DirectGuard.pushAt 180 0 0,
    DirectGuard.opAt 181 .CALLDATALOAD,
    DirectGuard.pushAt 182 0 0,
    DirectGuard.opAt 183 .BYTE,
    DirectGuard.pushAt 184 1 7,
    DirectGuard.opAt 185 .XOR,
    DirectGuard.pushAt 186 2 393 ]
private def byteJump : List Located := [DirectGuard.opAt 187 .JUMPI]
private def sizePrefix : List Located :=
  [ DirectGuard.pushAt 188 17 342276208914615837337402008677671501826,
    DirectGuard.opAt 189 .CALLDATASIZE,
    DirectGuard.opAt 190 .SHR,
    DirectGuard.pushAt 191 1 1,
    DirectGuard.opAt 192 .AND,
    DirectGuard.opAt 193 .ISZERO,
    DirectGuard.pushAt 194 2 393 ]
private def sizeJump : List Located := [DirectGuard.opAt 195 .JUMPI]
private def matchPath : List Located :=
  [ DirectGuard.pushAt 196 0 0,
    DirectGuard.pushAt 197 1 98,
    DirectGuard.opAt 198 .JUMP , DirectGuard.opAt 59 .JUMPDEST, DirectGuard.opAt 60 .POP ]
private def flag (input : ByteArray) : UInt256 :=
  UInt256.isZero (UInt256.land 1 (UInt256.shiftRight 342276208914615837337402008677671501826 (UInt256.ofNat input.size)))
private def byteState (input : ByteArray) : State :=
  PatternedScan.stS input 287 [393, byteValue input]
private def sizeEntry (input : ByteArray) : State := PatternedScan.stS input 288 []
private def sizeState (input : ByteArray) : State := PatternedScan.stS input 315 [393, flag input]
private theorem run_byte_prefix (input : ByteArray) :
    DirectGuard.run bytePrefix (DirectGuard.guardEntry input) = some (byteState input) := by
  simp [bytePrefix, byteState, byteValue, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.guardEntry, DirectGuard.atPC, DirectGuard.fallbackState,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
private theorem run_byte_fail (input : ByteArray) (hbyte : DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run byteJump (byteState input) = some (DirectGuard.fallbackState input) := by
  have h := byteValue_true input hbyte
  simp [byteJump, byteState, h, guard_fallback_dest, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.guardEntry, DirectGuard.atPC, DirectGuard.fallbackState,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
private theorem run_byte_match (input : ByteArray) (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run byteJump (byteState input) = some (sizeEntry input) := by
  have h := byteValue_zero input hbyte
  simp [byteJump, byteState, sizeEntry, h, UInt256.isTrue, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.guardEntry, DirectGuard.atPC, DirectGuard.fallbackState,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
private theorem run_size_prefix (input : ByteArray) :
    DirectGuard.run sizePrefix (sizeEntry input) = some (sizeState input) := by
  simp [sizePrefix, sizeEntry, sizeState, flag, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.guardEntry, DirectGuard.atPC, DirectGuard.fallbackState,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
private theorem flag_hit (input : ByteArray) (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) : flag input = 0 := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  have hf : flag input = sizeFlag input := h
  rw [hf, sizeFlag_hit input hsize]
  rfl
private theorem flag_fail (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) : flag input = 1 := by
  have h := SizeLookupFlag.flag (UInt256.ofNat input.size)
  rw [SizeLookupFlag.mask_literal] at h
  have hf : flag input = sizeFlag input := h
  rw [hf, sizeFlag_fail input hfit hsize]
  rfl
private theorem run_size_fail (input : ByteArray) (h : flag input = 1) :
    DirectGuard.run sizeJump (sizeState input) = some (DirectGuard.fallbackState input) := by
  simp [sizeJump, sizeState, h, UInt256.isTrue, guard_fallback_dest, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.guardEntry, DirectGuard.atPC, DirectGuard.fallbackState,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
private theorem run_size_match (input : ByteArray) (h : flag input = 0) :
    DirectGuard.run (sizeJump ++ matchPath) (sizeState input) = some (PatternedScan.patternedEntry input) := by
  simp [sizeJump, matchPath, sizeState, h, UInt256.isTrue, guard_match_dest, DirectGuard.run, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
    DirectGuard.guardEntry, DirectGuard.atPC, DirectGuard.fallbackState,
    PatternedScan.stS, PatternedScan.atPC, PatternedScan.patternedEntry,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]
def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) := by
  by_cases hb : DirectGuard.firstByte input = 7
  · have hs : input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32 := by tauto
    exact (sound bytePrefix (run_byte_prefix input)).trans
      ((sound byteJump (run_byte_match input hb)).trans
        ((sound sizePrefix (run_size_prefix input)).trans
          (sound sizeJump (run_size_fail input (flag_fail input hfit hs)))))
  · exact (sound bytePrefix (run_byte_prefix input)).trans
      (sound byteJump (run_byte_fail input hb))
def gasSteps_match (input : ByteArray) (_hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound bytePrefix (run_byte_prefix input)).trans
    ((sound byteJump (run_byte_match input hbyte)).trans
      ((sound sizePrefix (run_size_prefix input)).trans
        (sound (sizeJump ++ matchPath) (run_size_match input (flag_hit input hsize)))))
def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 56 ∨ input.size = 120 ∨ input.size = 63 ∨ input.size = 64 ∨ input.size = 65 ∨ input.size = 128 ∨ input.size = 119 ∨ input.size = 55 ∨ input.size = 1 ∨ input.size = 31 ∨ input.size = 32) (hbyte : DirectGuard.firstByte input = 7) :
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
    (hbad : (input.size ≠ 56 ∧ input.size ≠ 120 ∧ input.size ≠ 63 ∧ input.size ≠ 64 ∧ input.size ≠ 65 ∧ input.size ≠ 128 ∧ input.size ≠ 119 ∧ input.size ≠ 55 ∧ input.size ≠ 1 ∧ input.size ≠ 31 ∧ input.size ≠ 32) ∨
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
