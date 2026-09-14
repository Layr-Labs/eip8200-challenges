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

def branchProgram : List Instr := [.push 1 126, .op .JUMPI]

/-- Nineteen instructions at pc 0, ending at the conditional branch. -/
def guardProgram : List Instr := headerProgram ++ guardValueProgram ++ branchProgram

/-- Every width miss restores the unchanged legacy entry with an empty stack. -/
def missProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .op .POP, .op .POP, .push 2 709, .op .JUMP]

open WindowTwentyOnePositive (headerStack)

/-- Abstract location and jump facts; this module does not depend on the artifact. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  guard : WindowTwentyOneBinding.Block artifact fork 0 guardProgram
  miss : WindowTwentyOneBinding.Block artifact fork 126 missProgram
  missJump : Decode.isValidJumpDest artifact.code 126 = true
  legacyJump : Decode.isValidJumpDest artifact.code 709 = true

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
    (hjump : Decode.isValidJumpDest template.executionEnv.code 126 = true) :
    runInstructions branchProgram
      (framed template (UInt256.ofNat 22) (value :: [m, e, b])) =
      some (framed template
        (if value.toNat = 0 then UInt256.ofNat 25 else UInt256.ofNat 126) [m, e, b]) := by
  by_cases hv : value.toNat = 0 <;>
    simp [branchProgram, runInstructions, framed, Stepper.runInstr, UInt256.isTrue,
      hv, hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

/-- The header guard covers all byte arrays, including truncated headers. -/
theorem run_guard (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 126 = true) :
    runInstructions guardProgram (framed template (UInt256.ofNat 0) []) =
      some (framed template
        (if (WindowTwentyOneInput.guardDiff input).toNat = 0
          then UInt256.ofNat 25 else UInt256.ofNat 126) (headerStack input)) := by
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

theorem run_miss (template : State) (input : ByteArray)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 709 = true) :
    runInstructions missProgram (framed template (UInt256.ofNat 126) (headerStack input)) =
      some (framed template (UInt256.ofNat 709) []) := by
  simp [missProgram, runInstructions, framed, headerStack, Stepper.runInstr, hjump,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
