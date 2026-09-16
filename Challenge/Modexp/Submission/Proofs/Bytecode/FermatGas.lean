import Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

def withModulus (template : State) (input : ByteArray) (pc : UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) pc
    (WindowTwentyOneInput.modulusWord input :: coreStack input)

/-- The early entry at 25 with the header stack. -/
def entryState (template : State) (input : ByteArray) : State :=
  WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 25) (headerStack input)

/-- From the early entry at 25 every matching input reaches a returned state
with the specification result: through the Fermat exit when the exponent is
`p - 1` for one of the two special primes, and through the window core otherwise. -/
def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowTwentyOneGasRoute.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State, Nonempty (GasSteps (entryState template input) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 827 = true := by
    rw [ec.code]
    exact paths.legacyJump
  have hraw := FermatNext.run_entry (context template input)
    (UInt256.ofNat (baseSize input)) (UInt256.ofNat (exponentSize input))
    (UInt256.ofNat (modulusSize input)) hjump
  have heo : UInt256.ofNat 96 + UInt256.ofNat (baseSize input) = exponentOffset input := by
    rw [exponentOffset, Word.ofNat_add_ofNat (by have := hmatch.1; omega)]
  have hmo : exponentOffset input + UInt256.ofNat 32 = modulusOffset input := by
    rw [exponentOffset, modulusOffset, hmatch.2.1,
      Word.ofNat_add_ofNat (by have := hmatch.1; omega)]
  rw [heo, hmo, exponent_at template input hmatch.1, modulus_at template input hmatch] at hraw
  have hraw' : runInstructions FermatNext.entryProgram (entryState template input) =
      some (WindowTwentyOneEntry.framed (context template input)
        (if (FermatNext.fermatDiff m e).toNat = 0 then UInt256.ofNat 45 else UInt256.ofNat 827)
        (m :: coreStack input)) := hraw
  obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
    WindowTwentyOneGasRoute.handled legacy template env hcall input hmatch
  by_cases he : (FermatNext.fermatDiff m e).toNat = 0
  · rw [if_pos he] at hraw'
    have entrySteps : GasSteps (entryState template input)
        (withModulus template input (UInt256.ofNat 45)) :=
      paths.entry.steps (ec.transfer rfl rfl) rfl hraw'
    have hpraw := FermatNext.run_prime (context template input) m (coreStack input)
      (by simp [coreStack]) hjump
    by_cases hprime : (FermatProgram.primeValue m).toNat = 0
    · rw [if_pos hprime] at hpraw
      have primeSteps : GasSteps (withModulus template input (UInt256.ofNat 45))
          (WindowTwentyOneGasRoute.entryState template input) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      exact ⟨oldFinal, ⟨(entrySteps.trans primeSteps).trans oldTrace⟩, oldDone, oldResult⟩
    · rw [if_neg hprime] at hpraw
      have primeSteps : GasSteps (withModulus template input (UInt256.ofNat 45))
          (withModulus template input (UInt256.ofNat 96)) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have hmNat : m.toNat = WindowTwentyOneInput.modulusValue input :=
        WindowTwentyOneInput.modulusWord_toNat input
      have hp : (WindowTwentyOneInput.modulusValue input).Prime := by
        rw [← hmNat]
        rcases (FermatProgram.primeValue_nonzero m).mp hprime with h | h
        · rw [h]
          exact hbn
        · rw [h]
          exact hsecp
      have heq : m - UInt256.ofNat 1 = e := FermatNext.fermatDiff_zero m e he
      have hsub : (m - UInt256.ofNat 1).toNat = m.toNat - 1 := by
        have hm1 : 1 ≤ m.toNat := by have := hp.two_le; omega
        conv_lhs => rw [Word.word_eq_ofNat_toNat m]
        rw [Word.ofNat_sub_ofNat hm1 m.val.isLt, Word.word_toNat_ofNat]
        exact Nat.mod_eq_of_lt (by have hb : m.toNat < 2^256 := m.val.isLt; omega)
      have hexponent : WindowTwentyOneInput.exponentValue input =
          WindowTwentyOneInput.modulusValue input - 1 := by
        have h := congrArg UInt256.toNat heq
        rw [hsub, WindowTwentyOneInput.exponentWord_toNat, hmNat] at h
        exact h.symm
      let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 115)
        (FermatMath.resultWord input) 0 (coreStack input)
      have hr := FermatProgram.run_return (context template input) m
        (coreStack input) (baseSize input) hmatch.1 (by simp [coreStack]) rfl 0 (by decide) rfl
      change runInstructions FermatProgram.returnProgram
        (withModulus template input (UInt256.ofNat 96)) = some final at hr
      have resultSteps : GasSteps (withModulus template input (UInt256.ofNat 96)) final :=
        paths.result.steps (ec.transfer rfl rfl) rfl hr
      refine ⟨final, ⟨(entrySteps.trans primeSteps).trans resultSteps⟩, ?_, ?_⟩
      · change (true && template.callStack.isEmpty) = true
        rw [hcall]
        rfl
      · have h := WindowTwentyOneReturn.returned_result (context template input) (UInt256.ofNat 115)
          (FermatMath.resultWord input) 0 (coreStack input)
        rw [← FermatMath.result_spec input hmatch hp hexponent] at h
        exact h
  · rw [if_neg he] at hraw'
    have entrySteps : GasSteps (entryState template input)
        (WindowTwentyOneGasRoute.entryState template input) :=
      paths.entry.steps (ec.transfer rfl rfl) rfl hraw'
    exact ⟨oldFinal, ⟨entrySteps.trans oldTrace⟩, oldDone, oldResult⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
