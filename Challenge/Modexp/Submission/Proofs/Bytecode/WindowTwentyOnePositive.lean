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

def routeStack (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (baseSize input), UInt256.ofNat (exponentSize input),
   UInt256.ofNat (modulusSize input), UInt256.ofNat 96,
   exponentOffset input, modulusOffset input, UInt256.ofNat 1263,
   modulusOffset input, exponentOffset input, UInt256.ofNat (modulusSize input),
   UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)]

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

def prepareProgram : List Instr :=
  WindowTwentyOneEntry.baseProgram ++ WindowTwentyOneEntry.modulusProgram ++ WindowTwentyOneEntry.normalizeProgram

def normalized (template : State) (input : ByteArray) : State :=
  WindowTwentyOneTablePrelude.initial (context template input) (UInt256.ofNat 2662)
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input) (routeStack input)

theorem run_prepare (template : State) (input : ByteArray)
    (hmatch : WindowTwentyOneInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowTwentyOneInput.modulusWord input).toNat)
    (hzeroBase : Decode.isValidJumpDest template.executionEnv.code 3278 = true)
    (hzeroModulus : Decode.isValidJumpDest template.executionEnv.code 3270 = true) :
    runInstructions prepareProgram (state template input (UInt256.ofNat 2637)) =
      some (normalized template input) := by
  have hsmall : baseSize input < 2 ^ 256 := by have := hmatch.1; omega
  have hb : (UInt256.ofNat (baseSize input)).toNat ≠ 0 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]
    omega
  have hbr := WindowTwentyOneEntry.run_base (context template input) (UInt256.ofNat (baseSize input))
    (routeStack input) (by simp [routeStack]) rfl hzeroBase
  have hm := WindowTwentyOneEntry.run_modulus (context template input) (modulusOffset input)
    (routeStack input) (by simp [routeStack]) rfl hzeroModulus
  have hnr := WindowTwentyOneEntry.run_normalize (context template input)
    (WindowTwentyOneInput.modulusWord input) (UInt256.ofNat 96) (baseSize input) hmatch.1
    (routeStack input) (by simp [routeStack]) rfl rfl
  have hb' : runInstructions WindowTwentyOneEntry.baseProgram
      (state template input (UInt256.ofNat 2637)) =
      some (state template input (UInt256.ofNat 2644)) := by
    simpa only [state, if_neg hb] using hbr
  have hm' : runInstructions WindowTwentyOneEntry.modulusProgram
      (state template input (UInt256.ofNat 2644)) =
      some (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 2652)
        (WindowTwentyOneInput.modulusWord input :: routeStack input)) := by
    simpa only [state, modulus_at template input hmatch, if_neg (Nat.ne_of_gt hmodulus)] using hm
  have hn' : runInstructions WindowTwentyOneEntry.normalizeProgram
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 2652)
        (WindowTwentyOneInput.modulusWord input :: routeStack input)) =
      some (normalized template input) := by
    simpa only [normalized, WindowTwentyOneTablePrelude.initial, WindowTwentyOneEntry.framed,
      WindowTwentyOneInput.baseWord, context, List.cons_append, List.nil_append,
      show (UInt256.ofNat 96).toNat = 96 by decide] using hnr
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hb' hm') hn'

def program : List Instr := prepareProgram ++ WindowTwentyOneCore.program

def returned (template : State) (input : ByteArray) : State :=
  WindowTwentyOneCore.returnedState (context template input) (WindowTwentyOneInput.baseWord input)
    (WindowTwentyOneInput.modulusWord input) (WindowTwentyOneInput.exponentWord input) (routeStack input)

theorem run_positive (template : State) (input : ByteArray)
    (hmatch : WindowTwentyOneInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowTwentyOneInput.modulusWord input).toNat)
    (hzeroBase : Decode.isValidJumpDest template.executionEnv.code 3278 = true)
    (hzeroModulus : Decode.isValidJumpDest template.executionEnv.code 3270 = true)
    (hloop : Decode.isValidJumpDest template.executionEnv.code 2801 = true) :
    runInstructions program (state template input (UInt256.ofNat 2637)) =
      some (returned template input) := by
  have hp := run_prepare template input hmatch hbase hmodulus hzeroBase hzeroModulus
  have hc := WindowTwentyOneCore.run_core (context template input)
    (WindowTwentyOneInput.baseWord input) (WindowTwentyOneInput.modulusWord input)
    (exponentOffset input) (modulusOffset input) (routeStack input)
    (by simp [routeStack]) rfl rfl (modulus_at template input hmatch) hloop
  have hc' : runInstructions WindowTwentyOneCore.program (normalized template input) =
      some (returned template input) := by
    simpa only [normalized, returned, exponent_at template input hmatch.1] using hc
  exact runInstructions_append_some _ _ _ _ _ hp hc'

theorem returned_spec (template : State) (input : ByteArray)
    (hmatch : WindowTwentyOneInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowTwentyOneInput.modulusWord input).toNat) :
    (returned template input).toResult = .returned (spec input) := by
  have hm : WindowTwentyOneInput.modulusValue input ≠ 0 := by
    rw [WindowTwentyOneInput.modulusWord_toNat] at hmodulus
    omega
  rw [returned, WindowTwentyOneCore.core_result _ _ _ _ hmodulus,
    WindowTwentyOneInput.baseWord_toNat input hbase hmatch.1,
    WindowTwentyOneInput.exponentWord_toNat, WindowTwentyOneInput.modulusWord_toNat,
    WindowTwentyOneInput.spec_eq input hmatch, Algorithm.modPow_eq, if_neg hm]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOnePositive
