import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowTwentyOneEntry WindowNibbleKernel

/-- The early header reader and width guard at pc 0, leaving only `baseSize` on the stack. -/
def headerProgram : List Instr :=
  [.push 0 0, .op .CALLDATALOAD]

def guardValueProgram : List Instr :=
  [.push 1 32, .op (.Dup ⟨1, by decide⟩), .op .GT,
   .push 1 32, .op (.Dup ⟨0, by decide⟩), .op .CALLDATALOAD, .op .XOR, .op .OR,
   .push 1 64, .op .CALLDATALOAD, .push 1 32, .op .XOR, .op .OR]

def branchProgram : List Instr := [.push 1 127, .op .JUMPI]

/-- Seventeen instructions at pc 0, ending at the conditional branch. -/
def guardProgram : List Instr := headerProgram ++ guardValueProgram ++ branchProgram

/-- Every width miss drops the baseSize word and enters the fixed-vector
recogniser at pc 599 with an empty stack; two inert JUMPDESTs preserve downstream indices. -/
def missProgram : List Instr :=
  [.op .JUMPDEST, .op .POP, .push 2 599, .op .JUMP]

open WindowTwentyOnePositive (headerStack)

/-- Abstract location and jump facts; this module does not depend on the artifact. -/
structure Paths (artifact : ProgramArtifact) (fork : Fork) where
  guard : WindowTwentyOneBinding.Block artifact fork 0 guardProgram
  miss : WindowTwentyOneBinding.Block artifact fork 127 missProgram
  missJump : Decode.isValidJumpDest artifact.code 127 = true
  /-- The fixed-vector recogniser's entry, where the width miss now lands. -/
  legacyJump : Decode.isValidJumpDest artifact.code 599 = true

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
      some (framed template (UInt256.ofNat 2) (headerStack input)) := by
  simp [headerProgram, runInstructions, framed, Stepper.runInstr, headerStack, hdata,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, baseSize]
  rfl

theorem run_guard_value (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input) :
    runInstructions guardValueProgram
      (framed template (UInt256.ofNat 2) (headerStack input)) =
      some (framed template (UInt256.ofNat 19)
        (WindowTwentyOneInput.guardDiff input :: headerStack input)) := by
  have he : MachineState.readWord input 32 = UInt256.ofNat (exponentSize input) := rfl
  have hm : MachineState.readWord input 64 = UInt256.ofNat (modulusSize input) := rfl
  simp [guardValueProgram, runInstructions, framed, Stepper.runInstr,
    WindowTwentyOneInput.guardDiff, headerStack, hdata, he, hm,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat, baseSize, xor_comm]

theorem run_branch (template : State) (value b : UInt256)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 127 = true) :
    runInstructions branchProgram
      (framed template (UInt256.ofNat 19) (value :: [b])) =
      some (framed template
        (if value.toNat = 0 then UInt256.ofNat 22 else UInt256.ofNat 127) [b]) := by
  by_cases hv : value.toNat = 0 <;>
    simp [branchProgram, runInstructions, framed, Stepper.runInstr, UInt256.isTrue,
      hv, hjump, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
      Word.succ_ofNat_mod, Word.ofNat_add_mod]

/-- The header guard covers all byte arrays, including truncated headers. -/
theorem run_guard (template : State) (input : ByteArray)
    (hdata : template.executionEnv.calldata = input)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 127 = true) :
    runInstructions guardProgram (framed template (UInt256.ofNat 0) []) =
      some (framed template
        (if (WindowTwentyOneInput.guardDiff input).toNat = 0
          then UInt256.ofNat 22 else UInt256.ofNat 127) (headerStack input)) := by
  have hh := run_header template input hdata
  have hv := run_guard_value template input hdata
  have hb := run_branch template (WindowTwentyOneInput.guardDiff input)
    (UInt256.ofNat (baseSize input)) hjump
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
    (hjump : Decode.isValidJumpDest template.executionEnv.code 599 = true) :
    runInstructions missProgram (framed template (UInt256.ofNat 127) (headerStack input)) =
      some (framed template (UInt256.ofNat 599) []) := by
  simp [missProgram, runInstructions, framed, headerStack, Stepper.runInstr, hjump,
    Word.literal_eq_ofNat, Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram
