import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowTwentyOneEntry WindowNibbleKernel

/-- 0..12: the exponent and modulus size difference. -/
def sizeValueProgram : List Instr :=
  [.push 1 32, .op (.Dup ⟨0, by decide⟩), .op .CALLDATALOAD, .op .XOR,
   .push 1 64, .op .CALLDATALOAD, .push 1 32, .op .XOR, .op .OR]

def sizeBranchProgram : List Instr := [.push 2 578, .op .JUMPI]

/-- 0..16: the exponent and modulus size test. Any mismatch enters the fixed-vector
recogniser at 599 with an empty stack. -/
def sizeProgram : List Instr := sizeValueProgram ++ sizeBranchProgram

/-- 16..21: the base size difference. -/
def widthValueProgram : List Instr := [.push 0 0, .op .CALLDATALOAD, .push 1 32, .op .XOR]

def widthBranchProgram : List Instr := [.push 1 103, .op .JUMPI]

/-- 16..24: the base size test. A base size other than 32 enters the general-width
entry at 103 with an empty stack; 32 falls through to the fast entry at 24. -/
def widthTestProgram : List Instr := widthValueProgram ++ widthBranchProgram

def sizeDiff (input : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.xor (UInt256.ofNat 32) (UInt256.ofNat (modulusSize input)))
    (UInt256.xor (UInt256.ofNat (exponentSize input)) (UInt256.ofNat 32))

def baseDiff (input : ByteArray) : UInt256 :=
  UInt256.xor (UInt256.ofNat 32) (UInt256.ofNat (baseSize input))

/-- Abstract location and jump facts; this module does not depend on the artifact. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  size : WindowTwentyOneBinding.Block artifact fork 0 sizeProgram
  width : WindowTwentyOneBinding.Block artifact fork 16 widthTestProgram
  /-- The fixed-vector recogniser's entry, where a size miss lands. -/
  legacyJump : Decode.isValidJumpDest artifact.code 578 = true
  /-- The general-width entry. -/
  genJump : Decode.isValidJumpDest artifact.code 103 = true

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

theorem sizeDiff_eq_zero_iff (input : ByteArray) :
    sizeDiff input = 0 ↔ exponentSize input = 32 ∧ modulusSize input = 32 := by
  have he : exponentSize input < 2 ^ 256 := header_lt input 32
  have hm : modulusSize input < 2 ^ 256 := header_lt input 64
  simp only [sizeDiff, WindowGuardLogic.wordOr_eq_zero_iff, WindowGuardLogic.wordXor_eq_zero_iff]
  rw [eq_comm (a := UInt256.ofNat 32), ofNat_eq_32_iff _ hm, ofNat_eq_32_iff _ he]
  exact And.comm

theorem sizeDiff_zero_iff (input : ByteArray) :
    (sizeDiff input).toNat = 0 ↔ exponentSize input = 32 ∧ modulusSize input = 32 := by
  rw [← sizeDiff_eq_zero_iff]
  constructor
  · intro h
    exact Word.word_ext h
  · intro h
    rw [h]
    rfl

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
  have he : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
  have hm : MachineState.readWord input 64 = UInt256.ofNat (modulusSize input) := rfl
  simp [sizeValueProgram, runInstructions, framed, Stepper.runInstr, sizeDiff, hdata, he, hm,
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
    (hjump : Decode.isValidJumpDest template.executionEnv.code 103 = true) :
    runInstructions widthBranchProgram (framed template (UInt256.ofNat 21) [value]) =
      some (framed template
        (if value.toNat = 0 then UInt256.ofNat 24 else UInt256.ofNat 103) []) := by
  by_cases hv : value.toNat = 0 <;>
    simp [widthBranchProgram, runInstructions, framed, Stepper.runInstr, UInt256.isTrue,
      hv, hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_width (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 103 = true) :
    runInstructions widthTestProgram (framed template (UInt256.ofNat 16) []) =
      some (framed template
        (if (baseDiff input).toNat = 0 then UInt256.ofNat 24 else UInt256.ofNat 103) []) :=
  runInstructions_append_some _ _ _ _ _ (run_width_value template input hdata)
    (run_width_branch template (baseDiff input) hjump)

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
