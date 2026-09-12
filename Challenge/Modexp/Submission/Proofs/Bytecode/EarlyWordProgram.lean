import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowTwentyOneEntry WindowNibbleKernel

/-- The early header reader preserves every carrier field except PC and stack. -/
def headerProgram : List Instr :=
  [.push 0 0, .op .CALLDATALOAD,
   .push 1 32, .op .CALLDATALOAD, .push 1 64, .op .CALLDATALOAD]

def guardValueProgram : List Instr :=
  [.push 1 32, .op (.Dup ⟨3, by decide⟩), .op .GT,
   .op (.Dup ⟨2, by decide⟩), .push 1 32, .op .XOR, .op .OR,
   .op (.Dup ⟨1, by decide⟩), .push 1 32, .op .XOR, .op .OR]

def branchProgram : List Instr := [.push 2 47, .op .JUMPI]

/-- Twenty instructions at pc 5224, ending at the conditional branch. -/
def guardProgram : List Instr := headerProgram ++ guardValueProgram ++ branchProgram

def offsetsProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 1 96, .op .ADD,
   .op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .ADD]

def frameProgram : List Instr :=
  [.push 2 1186, .op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .push 1 96, .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨8, by decide⟩),
   .op (.Dup ⟨10, by decide⟩), .push 2 4955, .op .JUMP]

/-- Fifteen instructions at pc 5251, with the canonical return frame. -/
def hitProgram : List Instr := offsetsProgram ++ frameProgram

/-- Every width miss restores the unchanged legacy entry with an empty stack. -/
def missProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP, .op .POP, .push 2 1169, .op .JUMP]

def headerStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (baseSize input)]

/-- Abstract location and jump facts; this module does not depend on the artifact. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  guard : WindowTwentyOneBinding.Block artifact fork 0 guardProgram
  hit : WindowTwentyOneBinding.Block artifact fork 26 hitProgram
  miss : WindowTwentyOneBinding.Block artifact fork 47 missProgram
  missJump : Decode.isValidJumpDest artifact.code 47 = true
  hitJump : Decode.isValidJumpDest artifact.code 4955 = true
  legacyJump : Decode.isValidJumpDest artifact.code 1169 = true

/-- Context reset is valid only with the three explicit carrier premises. -/
theorem framed_eq_state (template : State) (input : ByteArray) (pc : UInt256)
    (hdata : template.executionEnv.calldata = input)
    (hmem : template.memory = ByteArray.empty)
    (hactive : template.activeWords = UInt256.ofNat 0) :
    framed template pc (WindowTwentyOnePositive.routeStack input) =
      WindowTwentyOnePositive.state template input pc := by
  simp only [WindowTwentyOnePositive.state, WindowTwentyOnePositive.context,
    ← hdata, ← hmem, ← hactive]

private theorem xor_comm (a b : UInt256) : UInt256.xor a b = UInt256.xor b a := by
  apply Word.word_ext
  change (a.val ^^^ b.val).val = (b.val ^^^ a.val).val
  rw [Fin.xor_val, Fin.xor_val, Nat.xor_comm]

theorem run_header (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input) :
    runInstructions headerProgram (framed template (UInt256.ofNat 0) []) =
      some (framed template (UInt256.ofNat 8) (headerStack input)) := by
  simp [headerProgram, runInstructions, framed, Stepper.runInstr, headerStack, hdata,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat, baseSize, exponentSize, modulusSize]
  exact ⟨rfl, rfl, rfl⟩

theorem run_guard_value (template : State) (b e m : UInt256) :
    runInstructions guardValueProgram (framed template (UInt256.ofNat 8) [m, e, b]) =
      some (framed template (UInt256.ofNat 22) (widthDiff b e m :: [m, e, b])) := by
  simp [guardValueProgram, runInstructions, framed, Stepper.runInstr, widthDiff,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod, xor_comm]

theorem run_branch (template : State) (value b e m : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 47 = true) :
    runInstructions branchProgram
      (framed template (UInt256.ofNat 22) (value :: [m, e, b])) =
      some (framed template
        (if value.toNat = 0 then UInt256.ofNat 26 else UInt256.ofNat 47) [m, e, b]) := by
  by_cases hv : value.toNat = 0 <;>
    simp [branchProgram, runInstructions, framed, Stepper.runInstr, UInt256.isTrue,
      hv, hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

/-- The header guard covers all byte arrays, including truncated headers. -/
theorem run_guard (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 47 = true) :
    runInstructions guardProgram (framed template (UInt256.ofNat 0) []) =
      some (framed template
        (if (WindowTwentyOneInput.guardDiff input).toNat = 0
          then UInt256.ofNat 26 else UInt256.ofNat 47) (headerStack input)) := by
  have hh := run_header template input hdata
  have hv := run_guard_value template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
  have hb := run_branch template (WindowTwentyOneInput.guardDiff input)
    (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input))
    (UInt256.ofNat (modulusSize input)) hjump
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hh hv) hb

/-- This uses the broad width predicate, not operand values or completeness. -/
theorem guard_zero_iff (input : ByteArray) :
    (WindowTwentyOneInput.guardDiff input).toNat = 0 ↔ WindowTwentyOneInput.Matches input := by
  rw [← WindowTwentyOneInput.guardDiff_eq_zero_iff]
  constructor
  · intro h
    exact Word.word_ext h
  · intro h
    rw [h]
    rfl

theorem run_offsets (template : State) (b e m : UInt256) :
    runInstructions offsetsProgram (framed template (UInt256.ofNat 26) [m, e, b]) =
      some (framed template (UInt256.ofNat 33)
        [UInt256.ofNat 96 + b + e, UInt256.ofNat 96 + b, m, e, b]) := by
  simp [offsetsProgram, runInstructions, framed, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod]

theorem run_frame (template : State) (b e m x y : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 4955 = true) :
    runInstructions frameProgram (framed template (UInt256.ofNat 33) [y, x, m, e, b]) =
      some (framed template (UInt256.ofNat 4955)
        [b, e, m, UInt256.ofNat 96, x, y, UInt256.ofNat 1186, y, x, m, e, b]) := by
  simp [frameProgram, runInstructions, framed, Stepper.runInstr, hjump,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat,
    Word.succ_ofNat_mod, Word.ofNat_add_mod]

/-- The hit frame is canonical without resetting memory or environment. -/
theorem run_hit (template : State) (input : ByteArray)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 4955 = true) :
    runInstructions hitProgram (framed template (UInt256.ofNat 26) (headerStack input)) =
      some (framed template (UInt256.ofNat 4955) (WindowTwentyOnePositive.routeStack input)) := by
  have ho := run_offsets template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
  have hf := run_frame template (UInt256.ofNat (baseSize input))
    (UInt256.ofNat (exponentSize input)) (UInt256.ofNat (modulusSize input))
    (UInt256.ofNat 96 + UInt256.ofNat (baseSize input))
    (UInt256.ofNat 96 + UInt256.ofNat (baseSize input) + UInt256.ofNat (exponentSize input)) hjump
  have both := runInstructions_append_some _ _ _ _ _ ho hf
  simpa only [hitProgram, headerStack, WindowTwentyOnePositive.routeStack,
    WindowTwentyOnePositive.exponentOffset, WindowTwentyOnePositive.modulusOffset,
    Word.ofNat_add_mod] using both

theorem run_miss (template : State) (input : ByteArray)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 1169 = true) :
    runInstructions missProgram (framed template (UInt256.ofNat 47) (headerStack input)) =
      some (framed template (UInt256.ofNat 1169) []) := by
  simp [missProgram, runInstructions, framed, headerStack, Stepper.runInstr, hjump,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
