import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowTwentyOneEntry WindowNibbleKernel

/-- 0..12: the exponent and modulus size difference. One unaligned load at 34 reads the
exponent size shifted left by 16 bits (its two high bytes and the modulus size's two high
bytes are zero for every valid tuple), the aligned load at 64 adds the modulus size, and
the sum is compared with `32 * 2^16 + 32`. -/
def sizeValueProgram : List Instr :=
  [.push 1 34, .op .CALLDATALOAD, .push 1 64, .op .CALLDATALOAD, .op .ADD,
   .push 3 0x200020, .op .XOR]

def sizeBranchProgram : List Instr := [.push 2 578, .op .JUMPI]

/-- 0..16: the exponent and modulus size test. Any mismatch enters the fixed-vector
recogniser at 599 with an empty stack. -/
def sizeProgram : List Instr := sizeValueProgram ++ sizeBranchProgram

/-- 16..21: the base size difference. -/
def widthValueProgram : List Instr := [.push 0 0, .op .CALLDATALOAD, .push 1 32, .op .XOR]

def widthBranchProgram : List Instr := [.push 1 101, .op .JUMPI]

/-- 16..24: the base size test. A base size other than 32 enters the general-width
entry at 103 with an empty stack; 32 falls through to the fast entry at 24. -/
def widthTestProgram : List Instr := widthValueProgram ++ widthBranchProgram

def sizeDiff (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 0x200020)
    (MachineState.readWord input 64 + MachineState.readWord input 34)

def baseDiff (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 32) (UInt256.ofNat (baseSize input))

/-- Abstract location and jump facts; this module does not depend on the artifact. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  size : WindowTwentyOneBinding.Block artifact fork 0 sizeProgram
  /-- The fixed-vector recogniser's entry, where a size miss lands. -/
  legacyJump : Decode.isValidJumpDest artifact.code 578 = true
  /-- The general-width entry. -/
  genJump : Decode.isValidJumpDest artifact.code 101 = true

theorem header_lt (input : ByteArray) (offset : Nat) :
    Precompile.bytesToNatPadded input offset 32 < 2 ^ 256 := by
  have h := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input offset 32
  simpa using h

private theorem ofNat_eq_32_iff (value : Nat) (hvalue : value < 2 ^ 256) :
    UInt256.ofNat value = UInt256.ofNat 32 ↔ value = 32 := by
  constructor
  · intro h
    have hv := congrArg UInt256.toNat h
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hvalue,
      Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)] at hv
    exact hv
  · rintro rfl
    rfl

/-- The unaligned word at 34: for exponent and modulus sizes below `2^240` it is the
exponent size shifted left by 16 bits. -/
theorem readWord34_toNat (input : ByteArray)
    (he : exponentSize input < 2 ^ 240) (hm : modulusSize input < 2 ^ 240) :
    (MachineState.readWord input 34).toNat = exponentSize input * 65536 := by
  rw [Bytes.readWord_toNat]
  have hsplit := Bytes.bytesToNatPadded_add input 34 30 2
  have hesplit := Bytes.bytesToNatPadded_add input 32 2 30
  have hmsplit := Bytes.bytesToNatPadded_add input 64 2 30
  have hlow := Bytes.bytesToNatPadded_lt_pow input 34 30
  have hmlow := Bytes.bytesToNatPadded_lt_pow input 66 30
  simp only [exponentSize, modulusSize] at he hm ⊢
  norm_num at hsplit hesplit hmsplit hlow hmlow he hm ⊢
  rw [hesplit] at he ⊢
  rw [hmsplit] at hm
  rw [hsplit]
  have h30 : (2 : Nat) ^ 240 = 256 ^ 30 := by norm_num
  have he0 : Precompile.bytesToNatPadded input 32 2 = 0 := by
    by_contra hne
    have hpos : 1 ≤ Precompile.bytesToNatPadded input 32 2 := Nat.one_le_iff_ne_zero.mpr hne
    have : 256 ^ 30 ≤ Precompile.bytesToNatPadded input 32 2 * 256 ^ 30 :=
      Nat.le_mul_of_pos_left _ hpos
    omega
  have hm0 : Precompile.bytesToNatPadded input 64 2 = 0 := by
    by_contra hne
    have hpos : 1 ≤ Precompile.bytesToNatPadded input 64 2 := Nat.one_le_iff_ne_zero.mpr hne
    have : 256 ^ 30 ≤ Precompile.bytesToNatPadded input 64 2 * 256 ^ 30 :=
      Nat.le_mul_of_pos_left _ hpos
    omega
  rw [he0, hm0]
  ring

/-- The size difference vanishes exactly for exponent and modulus sizes 32, for every
tuple whose two sizes are within the EIP-7823 bound. -/
theorem sizeDiff_zero_iff (input : ByteArray)
    (he : exponentSize input ≤ 1024) (hm : modulusSize input ≤ 1024) :
    (sizeDiff input).toNat = 0 ↔ exponentSize input = 32 ∧ modulusSize input = 32 := by
  have h34 := readWord34_toNat input (by omega) (by omega)
  have h64 : (MachineState.readWord input 64).toNat = modulusSize input :=
    Bytes.readWord_toNat input 64
  have hsum : (MachineState.readWord input 64 + MachineState.readWord input 34).toNat =
      modulusSize input + exponentSize input * 65536 := by
    rw [Word.word_toNat_add, h34, h64]
    exact Nat.mod_eq_of_lt (by omega)
  have hc : (UInt256.ofNat 0x200020).toNat = 0x200020 := by
    rw [Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by norm_num)
  constructor
  · intro h
    have hz : sizeDiff input = 0 := Word.word_ext h
    rw [sizeDiff, WindowGuardLogic.wordXor_eq_zero_iff] at hz
    have hn := congrArg UInt256.toNat hz
    rw [hc, hsum] at hn
    omega
  · rintro ⟨he32, hm32⟩
    have hw : UInt256.ofNat 0x200020 =
        MachineState.readWord input 64 + MachineState.readWord input 34 := by
      apply Word.word_ext
      rw [hc, hsum, he32, hm32]
    rw [sizeDiff, hw,
      (WindowGuardLogic.wordXor_eq_zero_iff _ _).mpr rfl]
    rfl

/-- Exponent and modulus sizes 32 always give a zero size difference. -/
theorem sizeDiff_zero_of (input : ByteArray)
    (hsize : exponentSize input = 32 ∧ modulusSize input = 32) :
    (sizeDiff input).toNat = 0 :=
  (sizeDiff_zero_iff input (by omega) (by omega)).mpr hsize

theorem baseDiff_eq_zero_iff (input : ByteArray) :
    baseDiff input = 0 ↔ baseSize input = 32 := by
  have hb : baseSize input < 2 ^ 256 := header_lt input 0
  rw [baseDiff, WindowGuardLogic.wordXor_eq_zero_iff, eq_comm, ofNat_eq_32_iff _ hb]

theorem baseDiff_zero_iff (input : ByteArray) :
    (baseDiff input).toNat = 0 ↔ baseSize input = 32 := by
  rw [← baseDiff_eq_zero_iff]
  constructor
  · intro h
    exact Word.word_ext h
  · intro h
    rw [h]
    rfl

theorem run_size_value (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input) :
    runInstructions sizeValueProgram (framed template (UInt256.ofNat 0) []) =
      some (framed template (UInt256.ofNat 12) [sizeDiff input]) := by
  simp [sizeValueProgram, runInstructions, framed, Stepper.runInstr, sizeDiff, hdata,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_size_branch (template : State) (value : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 578 = true) :
    runInstructions sizeBranchProgram (framed template (UInt256.ofNat 12) [value]) =
      some (framed template
        (if value.toNat = 0 then UInt256.ofNat 16 else UInt256.ofNat 578) []) := by
  by_cases hv : value.toNat = 0 <;>
    simp [sizeBranchProgram, runInstructions, framed, Stepper.runInstr, UInt256.isTrue,
      hv, hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

/-- The size test covers all byte arrays, including truncated headers. -/
theorem run_size (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 578 = true) :
    runInstructions sizeProgram (framed template (UInt256.ofNat 0) []) =
      some (framed template
        (if (sizeDiff input).toNat = 0 then UInt256.ofNat 16 else UInt256.ofNat 578) []) :=
  runInstructions_append_some _ _ _ _ _ (run_size_value template input hdata)
    (run_size_branch template (sizeDiff input) hjump)

theorem run_width_value (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input) :
    runInstructions widthValueProgram (framed template (UInt256.ofNat 16) []) =
      some (framed template (UInt256.ofNat 21) [baseDiff input]) := by
  have hb : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  have hz : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [widthValueProgram, runInstructions, framed, Stepper.runInstr, baseDiff, hdata, hb, hz,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat]

theorem run_width_branch (template : State) (value : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 101 = true) :
    runInstructions widthBranchProgram (framed template (UInt256.ofNat 21) [value]) =
      some (framed template
        (if value.toNat = 0 then UInt256.ofNat 24 else UInt256.ofNat 101) []) := by
  by_cases hv : value.toNat = 0 <;>
    simp [widthBranchProgram, runInstructions, framed, Stepper.runInstr, UInt256.isTrue,
      hv, hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_width (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 101 = true) :
    runInstructions widthTestProgram (framed template (UInt256.ofNat 16) []) =
      some (framed template
        (if (baseDiff input).toNat = 0 then UInt256.ofNat 24 else UInt256.ofNat 101) []) :=
  runInstructions_append_some _ _ _ _ _ (run_width_value template input hdata)
    (run_width_branch template (baseDiff input) hjump)

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
