import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineCore
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineEntry
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineInput

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNinePositive

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
   exponentOffset input, modulusOffset input, UInt256.ofNat 1267,
   modulusOffset input, exponentOffset input, UInt256.ofNat (modulusSize input),
   UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)]

def state (template : State) (input : ByteArray) (pc : UInt256) : State :=
  WindowNineEntry.framed (context template input) pc (routeStack input)

theorem exponent_at (template : State) (input : ByteArray) (hwidth : baseSize input ≤ 32) :
    MachineState.readWord (context template input).executionEnv.calldata
      (exponentOffset input).toNat = WindowNineInput.exponentWord input := by
  have hsmall : 96 + baseSize input < 2 ^ 256 := by omega
  simp only [context, exponentOffset, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, WindowNineInput.exponentWord]

theorem modulus_at (template : State) (input : ByteArray) (hmatch : WindowNineInput.Matches input) :
    MachineState.readWord (context template input).executionEnv.calldata
      (modulusOffset input).toNat = WindowNineInput.modulusWord input := by
  have hsmall : 96 + baseSize input + 32 < 2 ^ 256 := by have := hmatch.1; omega
  simp only [context, modulusOffset, hmatch.2.1, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hsmall, WindowNineInput.modulusWord]

def prepareProgram : List Instr :=
  WindowNineEntry.baseProgram ++ WindowNineEntry.modulusProgram ++ WindowNineEntry.normalizeProgram

def normalized (template : State) (input : ByteArray) : State :=
  WindowNineTablePrelude.initial (context template input) (UInt256.ofNat 3044)
    (WindowNineInput.baseWord input) (WindowNineInput.modulusWord input) (routeStack input)

theorem run_prepare (template : State) (input : ByteArray)
    (hmatch : WindowNineInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowNineInput.modulusWord input).toNat)
    (hzeroBase : Decode.isValidJumpDest template.executionEnv.code 3404 = true)
    (hzeroModulus : Decode.isValidJumpDest template.executionEnv.code 3396 = true) :
    runInstructions prepareProgram (state template input (UInt256.ofNat 3019)) =
      some (normalized template input) := by
  have hsmall : baseSize input < 2 ^ 256 := by have := hmatch.1; omega
  have hb : (UInt256.ofNat (baseSize input)).toNat ≠ 0 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hsmall]
    omega
  have hbr := WindowNineEntry.run_base (context template input) (UInt256.ofNat (baseSize input))
    (routeStack input) (by simp [routeStack]) rfl hzeroBase
  have hm := WindowNineEntry.run_modulus (context template input) (modulusOffset input)
    (routeStack input) (by simp [routeStack]) rfl hzeroModulus
  have hnr := WindowNineEntry.run_normalize (context template input)
    (WindowNineInput.modulusWord input) (UInt256.ofNat 96) (baseSize input) hmatch.1
    (routeStack input) (by simp [routeStack]) rfl rfl
  have hb' : runInstructions WindowNineEntry.baseProgram
      (state template input (UInt256.ofNat 3019)) =
      some (state template input (UInt256.ofNat 3026)) := by
    simpa only [state, if_neg hb] using hbr
  have hm' : runInstructions WindowNineEntry.modulusProgram
      (state template input (UInt256.ofNat 3026)) =
      some (WindowNineEntry.framed (context template input) (UInt256.ofNat 3034)
        (WindowNineInput.modulusWord input :: routeStack input)) := by
    simpa only [state, modulus_at template input hmatch, if_neg (Nat.ne_of_gt hmodulus)] using hm
  have hn' : runInstructions WindowNineEntry.normalizeProgram
      (WindowNineEntry.framed (context template input) (UInt256.ofNat 3034)
        (WindowNineInput.modulusWord input :: routeStack input)) =
      some (normalized template input) := by
    simpa only [normalized, WindowNineTablePrelude.initial, WindowNineEntry.framed,
      WindowNineInput.baseWord, context, List.cons_append, List.nil_append,
      show (UInt256.ofNat 96).toNat = 96 by decide] using hnr
  exact runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _ hb' hm') hn'

def program : List Instr := prepareProgram ++ WindowNineCore.program

def returned (template : State) (input : ByteArray) : State :=
  WindowNineCore.returnedState (context template input) (WindowNineInput.baseWord input)
    (WindowNineInput.modulusWord input) (WindowNineInput.exponentWord input) (routeStack input)

theorem run_positive (template : State) (input : ByteArray)
    (hmatch : WindowNineInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowNineInput.modulusWord input).toNat)
    (hzeroBase : Decode.isValidJumpDest template.executionEnv.code 3404 = true)
    (hzeroModulus : Decode.isValidJumpDest template.executionEnv.code 3396 = true)
    (hloop : Decode.isValidJumpDest template.executionEnv.code 3183 = true) :
    runInstructions program (state template input (UInt256.ofNat 3019)) =
      some (returned template input) := by
  have hp := run_prepare template input hmatch hbase hmodulus hzeroBase hzeroModulus
  have hc := WindowNineCore.run_core (context template input)
    (WindowNineInput.baseWord input) (WindowNineInput.modulusWord input)
    (exponentOffset input) (modulusOffset input) (routeStack input)
    (by simp [routeStack]) rfl rfl (modulus_at template input hmatch) hloop
  have hc' : runInstructions WindowNineCore.program (normalized template input) =
      some (returned template input) := by
    simpa only [normalized, returned, exponent_at template input hmatch.1] using hc
  exact runInstructions_append_some _ _ _ _ _ hp hc'

theorem returned_spec (template : State) (input : ByteArray)
    (hmatch : WindowNineInput.Matches input) (hbase : 0 < baseSize input)
    (hmodulus : 0 < (WindowNineInput.modulusWord input).toNat) :
    (returned template input).toResult = .returned (spec input) := by
  have hm : WindowNineInput.modulusValue input ≠ 0 := by
    rw [WindowNineInput.modulusWord_toNat] at hmodulus
    omega
  rw [returned, WindowNineCore.core_result _ _ _ _ hmodulus,
    WindowNineInput.baseWord_toNat input hbase hmatch.1,
    WindowNineInput.exponentWord_toNat, WindowNineInput.modulusWord_toNat,
    WindowNineInput.spec_eq input hmatch, Algorithm.modPow_eq, if_neg hm]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNinePositive
