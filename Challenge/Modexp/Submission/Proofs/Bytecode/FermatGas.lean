import Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatNext
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

def withModulus (template : State) (input : ByteArray) (tail : List UInt256)
    (pc : UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) pc
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)

/-- The join point at 31 with the core frame. -/
def joinState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  withModulus template input tail (UInt256.ofNat 31)

/-- From the join point at 31 every matching input reaches a returned state with the
specification result: through the Fermat exit when the exponent is `p - 1` for one of
the two special primes, and through the window core otherwise. -/
def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowTwentyOneGasRoute.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State, Nonempty (GasSteps (joinState template input tail) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 813 = true := by
    rw [ec.code]
    exact paths.routeJump
  have hraw := FermatNext.run_join (context template input) m e (shiftWord input :: tail)
    (by simp; omega) hjump
  obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
    WindowTwentyOneGasRoute.handled legacy template env hcall input tail htail hmatch
  by_cases he : (FermatNext.fermatDiff m e).toNat = 0
  · rw [if_pos he] at hraw
    have joinSteps : GasSteps (joinState template input tail)
        (withModulus template input tail (UInt256.ofNat 40)) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hraw
    have hpraw := FermatNext.run_prime (context template input) m (coreStack input tail)
      (by simp [coreStack]; omega) hjump
    by_cases hprime : (FermatProgram.primeValue m).toNat = 0
    · rw [if_pos hprime] at hpraw
      have primeSteps : GasSteps (withModulus template input tail (UInt256.ofNat 40))
          (WindowTwentyOneGasRoute.entryState template input tail) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      exact ⟨oldFinal, ⟨(joinSteps.trans primeSteps).trans oldTrace⟩, oldDone, oldResult⟩
    · rw [if_neg hprime] at hpraw
      have primeSteps : GasSteps (withModulus template input tail (UInt256.ofNat 40))
          (withModulus template input tail (UInt256.ofNat 90)) :=
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
      let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 102)
        (FermatMath.resultWord input) 0 (coreStack input tail)
      have hr := FermatProgram.run_return (context template input) m (shiftWord input)
        (coreStack input tail) (by simp [coreStack]; omega) rfl rfl
      change WindowTwentyOneMsize.runInstructionsX FermatProgram.returnProgram
        (withModulus template input tail (UInt256.ofNat 90)) = some final at hr
      have resultSteps : GasSteps (withModulus template input tail (UInt256.ofNat 90)) final :=
        WindowTwentyOneMsize.Block.stepsX paths.result (ec.transfer rfl rfl) rfl hr
      refine ⟨final, ⟨(joinSteps.trans primeSteps).trans resultSteps⟩, ?_, ?_⟩
      · change (true && template.callStack.isEmpty) = true
        rw [hcall]
        rfl
      · have h := WindowTwentyOneReturn.returned_result (context template input)
          (UInt256.ofNat 102) (FermatMath.resultWord input) 0 (coreStack input tail)
        rw [← FermatMath.result_spec input hmatch hp hexponent] at h
        exact h
  · rw [if_neg he] at hraw
    have joinSteps : GasSteps (joinState template input tail)
        (WindowTwentyOneGasRoute.entryState template input tail) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hraw
    exact ⟨oldFinal, ⟨joinSteps.trans oldTrace⟩, oldDone, oldResult⟩

/-- The fast entry at 24 (base size 32) builds the join frame with a zero shift. -/
def fastSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input = 32) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 24) [])
      (joinState template input []) := by
  have hraw := FermatNext.run_fast (context template input) [] (by simp)
  have hj : joinState template input [] =
      WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 31)
        [MachineState.readWord (context template input).executionEnv.calldata 160,
          MachineState.readWord (context template input).executionEnv.calldata 128,
          UInt256.ofNat 0] := by
    simp only [joinState, withModulus, coreStack, shiftWord, WindowTwentyOneInput.modulusWord,
      WindowTwentyOneInput.exponentWord, hb]
    rfl
  rw [hj]
  exact paths.fast.steps ((WindowTwentyOneGasRoute.context_env template env input).transfer rfl rfl)
    rfl hraw

/-- The general-width entry at 103 with a base size up to 32 builds the join frame
with the shift `8 * (32 - baseSize)` and leaves `32 - baseSize` under it. -/
def genSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input ≤ 32) (rest : List UInt256) (hrest : rest.length ≤ 980) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 103) rest)
      (joinState template input (UInt256.ofNat (32 - baseSize input) :: rest)) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  have h238 : Decode.isValidJumpDest (context template input).executionEnv.code 218 = true := by
    rw [ec.code]
    exact paths.bigJump
  have h31 : Decode.isValidJumpDest (context template input).executionEnv.code 31 = true := by
    rw [ec.code]
    exact paths.joinJump
  have hword : MachineState.readWord (context template input).executionEnv.calldata 0 =
      UInt256.ofNat (baseSize input) := rfl
  have hbig : baseSize input < 2 ^ 256 := by omega
  have hgt : (UInt256.gt (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)).toNat = 0 := by
    unfold UInt256.gt
    rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbig,
      Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
    simp [Nat.not_lt.mpr hb]
  have hc := FermatNext.run_gen_check (context template input) rest (by omega) h238
  rw [hword, if_pos hgt] at hc
  have hl := FermatNext.run_gen_load (context template input) (UInt256.ofNat (baseSize input)) rest
    (by omega) h31
  have hsub := Word.ofNat_sub_ofNat hb (by decide : 32 < 2 ^ 256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat (baseSize input))
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - baseSize input) * 8) := by
    rw [hsub, Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
    congr 1
  have hm160 : UInt256.ofNat 160 - UInt256.ofNat (32 - baseSize input) =
      UInt256.ofNat (96 + baseSize input + 32) := by
    rw [Word.ofNat_sub_ofNat (by omega) (by decide : 160 < 2 ^ 256)]
    congr 1
    omega
  have he128 : UInt256.ofNat 128 - UInt256.ofNat (32 - baseSize input) =
      UInt256.ofNat (96 + baseSize input) := by
    rw [Word.ofNat_sub_ofNat (by omega) (by decide : 128 < 2 ^ 256)]
    congr 1
    omega
  have hmn : (UInt256.ofNat (96 + baseSize input + 32)).toNat = 96 + baseSize input + 32 := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hen : (UInt256.ofNat (96 + baseSize input)).toNat = 96 + baseSize input := by
    rw [Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hshift, hsub, hm160, he128, hmn, hen] at hl
  have gc : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 103) rest)
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 114)
        (UInt256.ofNat (baseSize input) :: UInt256.ofNat 32 :: rest)) :=
    paths.genCheck.steps (ec.transfer rfl rfl) rfl hc
  have gl : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 114)
        (UInt256.ofNat (baseSize input) :: UInt256.ofNat 32 :: rest))
      (joinState template input (UInt256.ofNat (32 - baseSize input) :: rest)) :=
    paths.genLoad.steps (ec.transfer rfl rfl) rfl hl
  exact gc.trans gl

end Challenge.Modexp.Submission.Proofs.Bytecode.FermatGas
