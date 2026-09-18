import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInput

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def context (template : State) (input : ByteArray) : State :=
  { template with
    executionEnv := { template.executionEnv with calldata := input }
    memory := ByteArray.empty
    activeWords := UInt256.ofNat 0 }

def exponentOffset (input : ByteArray) : UInt256 := UInt256.ofNat (96 + baseSize input)
def modulusOffset (input : ByteArray) : UInt256 :=
  UInt256.ofNat (96 + baseSize input + exponentSize input)

/-- The three header sizes as the early entry at 26 sees them. -/
def headerStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (baseSize input)]

/-- The legacy route frame at 1759 (twelve words). -/
def routeStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
   exponentOffset input, modulusOffset input, UInt256.ofNat 1186,
   modulusOffset input, exponentOffset input, UInt256.ofNat (modulusSize input),
   UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)]

/-- The lean core frame built by the entry at 26: the exponent word, its offset
and the three header sizes.  The modulus word sits on top of it. -/
def coreStack (input : ByteArray) : List UInt256 :=
  [WindowTwentyOneInput.exponentWord input, exponentOffset input,
   UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (baseSize input)]

def state (template : State) (input : ByteArray) (pc : UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) pc (routeStack input)

theorem exponent_at (template : State) (input : ByteArray) (hwidth : baseSize input ≤ 32) :
    MachineState.readWord (context template input).executionEnv.calldata
      (exponentOffset input).toNat = WindowTwentyOneInput.exponentWord input := by
  have hsmall : 96 + baseSize input < 2 ^ 256 := by omega
  simp only [context, exponentOffset, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, WindowTwentyOneInput.exponentWord]

theorem modulus_at (template : State) (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) :
    MachineState.readWord (context template input).executionEnv.calldata
      (modulusOffset input).toNat = WindowTwentyOneInput.modulusWord input := by
  have hsmall : 96 + baseSize input + 32 < 2 ^ 256 := by have := hmatch.1; omega
  simp only [context, modulusOffset, hmatch.2.1, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, WindowTwentyOneInput.modulusWord]

def normalized (template : State) (input : ByteArray) : State :=
  WindowTwentyOneTablePrelude.initial (context template input) (UInt256.ofNat 879)
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input)
    (WindowTwentyOneInput.modulusWord input :: coreStack input)

def returned (template : State) (input : ByteArray) : State :=
  WindowTwentyOneCore.returnedState (context template input) (WindowTwentyOneInput.baseWord input)
    (WindowTwentyOneInput.modulusWord input) (WindowTwentyOneInput.exponentWord input)
    (WindowTwentyOneInput.modulusWord input :: coreStack input)

/-- The core result is the specification for every accepted input, including a
zero modulus, where the final `MULMOD` produces the zero word. -/
theorem returned_spec (template : State) (input : ByteArray)
    (hmatch : WindowTwentyOneInput.Matches input) :
    (returned template input).toResult = .returned (spec input) := by
  by_cases hmodulus : (WindowTwentyOneInput.modulusWord input).toNat = 0
  · have hm0 : WindowTwentyOneInput.modulusValue input = 0 := by
      rw [← WindowTwentyOneInput.modulusWord_toNat]
      exact hmodulus
    rw [returned, WindowTwentyOneCore.core_result_zero _ _ _ _ hmodulus,
      WindowTwentyOneInput.spec_eq input hmatch, Algorithm.modPow_eq, hm0, if_pos rfl]
  · have hpos : 0 < (WindowTwentyOneInput.modulusWord input).toNat := Nat.pos_of_ne_zero hmodulus
    have hm : WindowTwentyOneInput.modulusValue input ≠ 0 := by
      rw [WindowTwentyOneInput.modulusWord_toNat] at hmodulus
      exact hmodulus
    rw [returned, WindowTwentyOneCore.core_result _ _ _ _ hpos,
      WindowTwentyOneInput.baseWord_toNat_of_le input hmatch.1,
      WindowTwentyOneInput.exponentWord_toNat, WindowTwentyOneInput.modulusWord_toNat,
      WindowTwentyOneInput.spec_eq input hmatch, Algorithm.modPow_eq, if_neg hm]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
