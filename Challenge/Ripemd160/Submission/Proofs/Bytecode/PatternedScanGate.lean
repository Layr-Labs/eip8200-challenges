import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Data

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-!
# The first-byte gate at the scan entry

    0x88  JUMPDEST
    0x89  PUSH0 CALLDATALOAD PUSH1 f8 SHR      -- the first calldata byte
    0x8e  PUSH1 07 XOR                         -- zero exactly when it is 7
    0x91  PUSH2 016c JUMPI                     -- otherwise straight to the program
    0x95  PUSH1 ff PUSH0 NOT DIV ...           -- the scan setup, unchanged

Every stored vector starts with the byte 7, so the gate never diverts a hit; a calldata
whose first byte is not 7 skips the scan and continues at the program entry `0x16c`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanGate

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan

/-- The first calldata byte, as the first word shifted down. -/
def firstByte (input : ByteArray) : UInt256 :=
  UInt256.shiftRight (MachineState.readWord input 0) 248

/-- The `JUMPI` condition word. -/
def gateWord (input : ByteArray) : UInt256 := UInt256.xor 7 (firstByte input)

private theorem refW_eq (input : ByteArray) :
    MachineState.readWord input ((⟨0⟩ : UInt256).toNat) = MachineState.readWord input 0 := rfl

private theorem fallbackDest : Decode.isValidJumpDest submissionBytecode 364 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 201 (by rfl)

theorem xor_toNat (a b : UInt256) : (UInt256.xor a b).toNat = a.toNat ^^^ b.toNat := by
  rcases a with ⟨⟨x, hx⟩⟩
  rcases b with ⟨⟨y, hy⟩⟩
  show (x ^^^ y) % UInt256.size = x ^^^ y
  have hx' : x < 2 ^ 256 := hx
  have hy' : y < 2 ^ 256 := hy
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow hx' hy')

/-- The gate word is true exactly when the first byte is not 7. -/
theorem gateWord_isTrue_iff (input : ByteArray) :
    UInt256.isTrue (gateWord input) ↔ firstByte input ≠ 7 := by
  have h1 : (gateWord input).toNat = 7 ^^^ (firstByte input).toNat := by
    show (UInt256.xor 7 (firstByte input)).toNat = _
    rw [xor_toNat]
    rfl
  unfold UInt256.isTrue
  rw [h1]
  constructor
  · intro h heq
    apply h
    rw [heq]
    decide
  · intro hne h0
    apply hne
    apply Challenge.EvmProof.Word.word_ext
    have hcancel : (firstByte input).toNat = 7 ^^^ (7 ^^^ (firstByte input).toNat) := by
      rw [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
    rw [hcancel, h0, Nat.xor_zero]
    rfl

/-! ### The first byte of the stored vectors -/

theorem patterned_firstByte : firstByte PatternedInputData.patternedInput = 7 := by
  show UInt256.shiftRight (MachineState.readWord PatternedInputData.patternedInput 0)
    (UInt256.ofNat 248) = UInt256.ofNat 7
  have hshift := Challenge.EvmProof.Bytes.shiftRight_readWord
    PatternedInputData.patternedInput 0 1 (by omega) (by omega)
  have hbyte : EVM.Precompile.bytesToNatPadded PatternedInputData.patternedInput 0 1 = 7 := by
    rw [Challenge.EvmProof.Bytes.bytesToNatPadded_succ,
      Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width, Nat.zero_mul, Nat.zero_add,
      Nat.add_zero, PatternedWordLogic.byteFrom_patterned]
    rfl
  rw [show (32 - 1) * 8 = 248 from by norm_num] at hshift
  rw [hshift, hbyte]

theorem expected0_firstByte :
    UInt256.shiftRight (PatternedWordData.expectedWordAt 0) 248 = 7 := by
  rw [← PatternedWordLogic.readWord_patterned 0, Nat.mul_zero]
  exact patterned_firstByte

theorem data64_firstByte : firstByte Prefix64Data.data = 7 := by
  show UInt256.shiftRight (MachineState.readWord Prefix64Data.data (32 * 0)) 248 = 7
  rw [Prefix64Data.readWord_data 0 (by decide)]
  exact expected0_firstByte

theorem data128_firstByte : firstByte Prefix128Data.data = 7 := by
  show UInt256.shiftRight (MachineState.readWord Prefix128Data.data (32 * 0)) 248 = 7
  rw [Prefix128Data.readWord_data 0 (by decide)]
  exact expected0_firstByte

theorem data256_firstByte : firstByte Prefix256Data.data = 7 := by
  show UInt256.shiftRight (MachineState.readWord Prefix256Data.data (32 * 0)) 248 = 7
  rw [Prefix256Data.readWord_data 0 (by decide)]
  exact expected0_firstByte

/-! ### Stepping through the gate -/

/-- From the scan entry through the eight gate instructions, up to the `JUMPI`. -/
def gasSteps_gate (input : ByteArray) :
    GasSteps (patternedEntry input) (stS input 0x94 [364, gateWord input]) := by
  have a := soundS (opAt 64 .JUMPDEST)
    (blockOfS _ (pcFactS input 64 0x88 [] (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_jumpdest input 0x88 [] (by simp) (by norm_num)))
  have b := soundS (pushAt 65 0 0)
    (blockOfS _ (pcFactS input 65 0x89 [] (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_push0 input 0x89 [] (by simp) (by norm_num)))
  have c := soundS (opAt 66 .CALLDATALOAD)
    (blockOfS _ (pcFactS input 66 0x8a _ (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_calldataload input 0x8a ⟨0⟩ [] (by simp) (by norm_num)))
  rw [refW_eq] at c
  have d := soundS (pushAt 67 1 248)
    (blockOfS _ (pcFactS input 67 0x8b _ (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_push input 0x8b 1 248 [MachineState.readWord input 0]
        (by simp) (by decide) (by decide) (by norm_num)))
  have e := soundS (opAt 68 .SHR)
    (blockOfS _ (pcFactS input 68 0x8d _ (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_shr input 0x8d 248 (MachineState.readWord input 0) [] (by simp) (by norm_num)))
  have f := soundS (pushAt 69 1 7)
    (blockOfS _ (pcFactS input 69 0x8e _ (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_push input 0x8e 1 7 [firstByte input]
        (by simp) (by decide) (by decide) (by norm_num)))
  have g := soundS (opAt 70 .XOR)
    (blockOfS _ (pcFactS input 70 0x90 _ (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_xor input 0x90 7 (firstByte input) [] (by simp) (by norm_num)))
  have h := soundS (pushAt 71 2 364)
    (blockOfS _ (pcFactS input 71 0x91 _ (by norm_num)
        (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
      (stepS_push input 0x91 2 364 [gateWord input]
        (by simp) (by decide) (by decide) (by norm_num)))
  exact a.trans (b.trans (c.trans (d.trans (e.trans (f.trans (g.trans h))))))

/-- First byte 7: the `JUMPI` falls through into the scan setup at `0x95`. -/
def gasSteps_pass (input : ByteArray) (h7 : firstByte input = 7) :
    GasSteps (patternedEntry input) (atPC input 0x95) := by
  have hc : ¬ UInt256.isTrue (gateWord input) :=
    fun h => (gateWord_isTrue_iff input).1 h h7
  exact (gasSteps_gate input).trans
    (soundS (opAt 72 .JUMPI)
      (blockOfS _ (pcFactS input 72 0x94 _ (by norm_num)
          (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
        (stepS_jumpi_fall input 0x94 364 (gateWord input) [] (by simp) (by norm_num) hc)))

/-- First byte not 7: the `JUMPI` is taken to the program entry. -/
def gasSteps_exit (input : ByteArray) (h7 : firstByte input ≠ 7) :
    GasSteps (patternedEntry input) (fallbackState input) := by
  have hc : UInt256.isTrue (gateWord input) := (gateWord_isTrue_iff input).2 h7
  exact (gasSteps_gate input).trans
    (soundS (opAt 72 .JUMPI)
      (blockOfS _ (pcFactS input 72 0x94 _ (by norm_num)
          (by rw [Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactByteLength.instructionPC_eq_byteLength]; rfl))
        (stepS_jumpi_taken input 0x94 364 364 (gateWord input) []
          (by simp) (by norm_num) rfl hc fallbackDest)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanGate
