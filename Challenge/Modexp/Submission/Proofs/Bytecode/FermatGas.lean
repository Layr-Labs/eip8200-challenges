import Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatProgram
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

def withModulus (template : State) (input : ByteArray) (pc : UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) pc
    (WindowTwentyOneInput.modulusWord input :: routeStack input)

def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatProgram.Paths artifact fork) (legacy : WindowTwentyOneGasRoute.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State, Nonempty (GasSteps (state template input (UInt256.ofNat 4752)) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 2066 = true := by
    rw [ec.code]
    exact paths.legacyJump
  have hpraw := FermatProgram.run_prime (context template input) (modulusOffset input)
    (routeStack input) (by simp [routeStack]) (by simp [routeStack]) hjump
  rw [modulus_at template input hmatch] at hpraw
  obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
    WindowTwentyOneGasRoute.handled legacy template env hcall input hmatch
  by_cases hprime : (FermatProgram.primeValue m).toNat = 0
  · rw [if_pos hprime] at hpraw
    have headSteps : GasSteps (state template input (UInt256.ofNat 4752))
        (WindowTwentyOneGasRoute.entryState template input) :=
      paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
    exact ⟨oldFinal, ⟨headSteps.trans oldTrace⟩, oldDone, oldResult⟩
  · rw [if_neg hprime] at hpraw
    have headSteps : GasSteps (state template input (UInt256.ofNat 4752))
        (withModulus template input (UInt256.ofNat 4805)) :=
      paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
    have heraw := FermatProgram.run_exponent (context template input) m (exponentOffset input)
      (routeStack input) (by simp [routeStack]) (by simp [routeStack]) hjump
    rw [exponent_at template input hmatch.1] at heraw
    by_cases he : (UInt256.eq (m - UInt256.ofNat 1) (WindowTwentyOneInput.exponentWord input)).toNat = 0
    · rw [if_pos he] at heraw
      have expSteps : GasSteps (withModulus template input (UInt256.ofNat 4805))
          (WindowTwentyOneGasRoute.entryState template input) :=
        paths.exponent.steps (ec.transfer rfl rfl) rfl heraw
      exact ⟨oldFinal, ⟨(headSteps.trans expSteps).trans oldTrace⟩, oldDone, oldResult⟩
    · rw [if_neg he] at heraw
      have expSteps : GasSteps (withModulus template input (UInt256.ofNat 4805))
          (withModulus template input (UInt256.ofNat 4817)) :=
        paths.exponent.steps (ec.transfer rfl rfl) rfl heraw
      have hmNat : m.toNat = WindowTwentyOneInput.modulusValue input :=
        WindowTwentyOneInput.modulusWord_toNat input
      have hp : (WindowTwentyOneInput.modulusValue input).Prime := by
        rw [← hmNat]
        rcases (FermatProgram.primeValue_nonzero m).mp hprime with h | h
        · rw [h]
          exact hbn
        · rw [h]
          exact hsecp
      have heq : m - UInt256.ofNat 1 = WindowTwentyOneInput.exponentWord input := by
        by_contra hn
        have hz := (FermatProgram.eq_zero_iff _ _).mpr hn
        apply he
        rw [hz]
        rfl
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
      let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 4835)
        (FermatMath.resultWord input) 0 (routeStack input)
      have hr := FermatProgram.run_return (context template input) m (UInt256.ofNat 96)
        (routeStack input) (baseSize input) hmatch.1 (by simp [routeStack])
        (by simp [routeStack]) (by simp [routeStack]) 0 (by decide) rfl
      change runInstructions FermatProgram.returnProgram
        (withModulus template input (UInt256.ofNat 4817)) = some final at hr
      have resultSteps : GasSteps (withModulus template input (UInt256.ofNat 4817)) final :=
        paths.result.steps (ec.transfer rfl rfl) rfl hr
      refine ⟨final, ⟨(headSteps.trans expSteps).trans resultSteps⟩, ?_, ?_⟩
      · change (true && template.callStack.isEmpty) = true
        rw [hcall]
        rfl
      · have h := WindowTwentyOneReturn.returned_result (context template input) (UInt256.ofNat 4835)
          (FermatMath.resultWord input) 0 (routeStack input)
        rw [← FermatMath.result_spec input hmatch hp hexponent] at h
        exact h

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
