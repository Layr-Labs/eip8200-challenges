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
    ∃ final : State, Nonempty (GasSteps (state template input (UInt256.ofNat 5178)) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 5261 = true := by
    rw [ec.code]
    exact paths.missJump
  have hlegacyJump : Decode.isValidJumpDest (context template input).executionEnv.code 2657 = true := by
    rw [ec.code]
    exact paths.legacyJump
  have hlraw := FermatProgram.run_load (context template input) (modulusOffset input)
    (routeStack input) (by simp [routeStack]) (by simp [routeStack])
  rw [modulus_at template input hmatch] at hlraw
  have loadSteps : GasSteps (state template input (UInt256.ofNat 5178))
      (withModulus template input (UInt256.ofNat 5181)) :=
    paths.load.steps (ec.transfer rfl rfl) rfl hlraw
  have heraw := FermatProgram.run_exponentXor (context template input) m (exponentOffset input)
    (routeStack input) (by simp [routeStack]) (by simp [routeStack]) hjump
  rw [exponent_at template input hmatch.1] at heraw
  have hmraw := FermatProgram.run_miss (context template input) m (routeStack input)
    (by simp [routeStack]) hlegacyJump
  have missSteps : GasSteps (withModulus template input (UInt256.ofNat 5261))
      (state template input (UInt256.ofNat 2657)) :=
    paths.miss.steps (ec.transfer rfl rfl) rfl hmraw
  obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
    WindowTwentyOneGasRoute.handled legacy template env hcall input hmatch
  by_cases he : (UInt256.xor (m - UInt256.ofNat 1) (WindowTwentyOneInput.exponentWord input)).toNat = 0
  · rw [if_pos he] at heraw
    have expSteps : GasSteps (withModulus template input (UInt256.ofNat 5181))
        (withModulus template input (UInt256.ofNat 5192)) :=
      paths.exponent.steps (ec.transfer rfl rfl) rfl heraw
    have hpraw := FermatProgram.run_primeFilter (context template input) m (routeStack input)
      (by simp [routeStack]) hjump
    by_cases hprime : (FermatProgram.primeValue m).toNat = 0
    · rw [if_pos hprime] at hpraw
      have primeSteps : GasSteps (withModulus template input (UInt256.ofNat 5192))
          (withModulus template input (UInt256.ofNat 5261)) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      exact ⟨oldFinal, ⟨(((loadSteps.trans expSteps).trans primeSteps).trans missSteps).trans oldTrace⟩,
        oldDone, oldResult⟩
    · rw [if_neg hprime] at hpraw
      have primeSteps : GasSteps (withModulus template input (UInt256.ofNat 5192))
          (withModulus template input (UInt256.ofNat 5242)) :=
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
      have heq : m - UInt256.ofNat 1 = WindowTwentyOneInput.exponentWord input := by
        apply (WindowGuardLogic.wordXor_eq_zero_iff _ _).mp
        exact Word.word_ext he
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
      let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 5260)
        (FermatMath.resultWord input) 0 (routeStack input)
      have hr := FermatProgram.run_return (context template input) m (UInt256.ofNat 96)
        (routeStack input) (baseSize input) hmatch.1 (by simp [routeStack])
        (by simp [routeStack]) (by simp [routeStack]) 0 (by decide) rfl
      change runInstructions FermatProgram.returnProgram
        (withModulus template input (UInt256.ofNat 5242)) = some final at hr
      have resultSteps : GasSteps (withModulus template input (UInt256.ofNat 5242)) final :=
        paths.result.steps (ec.transfer rfl rfl) rfl hr
      refine ⟨final, ⟨((loadSteps.trans expSteps).trans primeSteps).trans resultSteps⟩, ?_, ?_⟩
      · change (true && template.callStack.isEmpty) = true
        rw [hcall]
        rfl
      · have h := WindowTwentyOneReturn.returned_result (context template input) (UInt256.ofNat 5260)
          (FermatMath.resultWord input) 0 (routeStack input)
        rw [← FermatMath.result_spec input hmatch hp hexponent] at h
        exact h
  · rw [if_neg he] at heraw
    have expSteps : GasSteps (withModulus template input (UInt256.ofNat 5181))
        (withModulus template input (UInt256.ofNat 5261)) :=
      paths.exponent.steps (ec.transfer rfl rfl) rfl heraw
    exact ⟨oldFinal, ⟨((loadSteps.trans expSteps).trans missSteps).trans oldTrace⟩, oldDone, oldResult⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
