import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.FermatMath
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FermatNext
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGasRoute
import Challenge.Modexp.Submission.Proofs.Bytecode.EarlyWordProgram

noncomputable section
set_option warningAsError true

namespace CycleSubmission.Global.FermatGas
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open HistoricalSearch
open WindowNibbleKernel WindowTwentyOneBinding WindowTwentyOnePositive

def withModulus (template : State) (input : ByteArray) (tail : List UInt256)
    (pc : UInt256) : State :=
  WindowTwentyOneEntry.framed (context template input) pc
    (WindowTwentyOneInput.modulusWord input :: coreStack input tail)

/-- The join point at 47 with the core frame. -/
def joinState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  withModulus template input tail (UInt256.ofNat 47)

private def fermatHandled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime)
    (he : (FermatNext.fermatDiff (WindowTwentyOneInput.modulusWord input)
      (WindowTwentyOneInput.exponentWord input)).toNat = 0)
    (hprime : (FermatProgram.primeValue (WindowTwentyOneInput.modulusWord input)).toNat ≠ 0) :
    ∃ final : State, Nonempty (GasSteps (withModulus template input tail 4848) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
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
  let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 4856)
    (FermatMath.resultWord input) 0 (coreStack input tail)
  have hr := FermatProgram.run_return (context template input) m (shiftWord input)
    (coreStack input tail) (by simp [coreStack]; omega) rfl rfl
  change WindowTwentyOneMsize.runInstructionsX FermatProgram.returnProgram
    (withModulus template input tail (UInt256.ofNat 4848)) = some final at hr
  have resultSteps : GasSteps (withModulus template input tail (UInt256.ofNat 4848)) final :=
    WindowTwentyOneMsize.Block.stepsX paths.result (ec.transfer rfl rfl) rfl hr
  refine ⟨final, ⟨resultSteps⟩, ?_, ?_⟩
  · change (true && template.callStack.isEmpty) = true
    rw [hcall]
    rfl
  · have h := WindowTwentyOneReturn.returned_result (context template input)
      (UInt256.ofNat 4856) (FermatMath.resultWord input) 0 (coreStack input tail)
    rw [← FermatMath.result_spec input hmatch hp hexponent] at h
    exact h

/-- Boundary facts choose an existing Fermat result or the complete window route. -/
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
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 745 = true := by
    rw [ec.code]; exact paths.routeJump
  have htailjump : Decode.isValidJumpDest (context template input).executionEnv.code 4847 = true := by
    rw [ec.code]; exact paths.tailJump
  have hprimejump : Decode.isValidJumpDest (context template input).executionEnv.code 10698 = true := by
    rw [ec.code]; exact paths.primeJump
  have hraw := FermatNext.run_join (context template input) m e (shiftWord input :: tail)
    (by simp; omega) hjump
  obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
    WindowTwentyOneGasRoute.handled legacy template env hcall input tail htail hmatch
  by_cases hs : (FermatNext.fermatDiff m e).toNat = 0
  · rw [if_pos hs] at hraw
    have joinSteps : GasSteps (joinState template input tail) (withModulus template input tail 56) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hraw
    have hjp := FermatNext.run_toPrime (context template input) (m :: coreStack input tail)
      (by simp [coreStack]; omega) hprimejump
    have toPrimeSteps : GasSteps (withModulus template input tail 56) (withModulus template input tail 10698) :=
      paths.toPrime.steps (ec.transfer rfl rfl) rfl hjp
    have hpraw := FermatNext.run_prime (context template input) m (coreStack input tail)
      (by simp [coreStack]; omega) htailjump
    have commonSteps := joinSteps.trans toPrimeSteps
    by_cases hp : (FermatProgram.primeValue m).toNat = 0
    · rw [if_pos hp] at hpraw
      have primeSteps : GasSteps (withModulus template input tail 10698) (withModulus template input tail 10748) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have hjraw := FermatNext.run_jumpTail (context template input) (m :: coreStack input tail)
        (by simp [coreStack]; omega) hjump
      have jumpSteps : GasSteps (withModulus template input tail 10748)
          (WindowTwentyOneGasRoute.entryState template input tail) :=
        paths.jumpTail.steps (ec.transfer rfl rfl) rfl hjraw
      exact ⟨oldFinal, ⟨((commonSteps.trans primeSteps).trans jumpSteps).trans oldTrace⟩, oldDone, oldResult⟩
    · rw [if_neg hp] at hpraw
      have primeSteps : GasSteps (withModulus template input tail 10698) (withModulus template input tail 4847) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have htraw := FermatNext.run_tail (context template input) m e (shiftWord input :: tail)
        (by simp; omega)
      have tailSteps : GasSteps (withModulus template input tail 4847) (withModulus template input tail 4848) :=
        paths.tail.steps (ec.transfer rfl rfl) rfl htraw
      obtain ⟨final, ⟨trace⟩, done, result⟩ :=
        fermatHandled paths template env hcall input tail htail hmatch hbn hsecp hs hp
      exact ⟨final, ⟨((commonSteps.trans primeSteps).trans tailSteps).trans trace⟩, done, result⟩
  · rw [if_neg hs] at hraw
    have joinSteps : GasSteps (joinState template input tail) (WindowTwentyOneGasRoute.entryState template input tail) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hraw
    exact ⟨oldFinal, ⟨joinSteps.trans oldTrace⟩, oldDone, oldResult⟩

/-- The loads at 16 (base size 32) build the core frame at the merged test (25). -/
def fastSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input = 32) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 16) [])
      (withModulus template input [] (UInt256.ofNat 25)) := by
  have hraw := FermatNext.run_fast (context template input) [] (by simp)
  have hj : withModulus template input [] (UInt256.ofNat 25) =
      WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 25)
        [MachineState.readWord (context template input).executionEnv.calldata 160,
          MachineState.readWord (context template input).executionEnv.calldata 128,
          MachineState.readWord (context template input).executionEnv.calldata 96] := by
    have hs : UInt256.shiftRight (MachineState.readWord input 96) (UInt256.ofNat 0) =
        MachineState.readWord input 96 := by
      apply Word.word_ext
      rw [Word.shiftRight_toNat _ (by norm_num)]
      simp
    simp only [withModulus, coreStack, shiftWord, WindowTwentyOneInput.modulusWord,
      WindowTwentyOneInput.exponentWord, WindowTwentyOneInput.baseWord, hb, Nat.sub_self,
      Nat.zero_mul, hs]
    rfl
  rw [hj]
  exact paths.fast.steps ((WindowTwentyOneGasRoute.context_env template env input).transfer rfl rfl)
    rfl hraw

private theorem word_toNat_mul (a b : UInt256) : (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl

private theorem ofNat_one_mul (x : UInt256) : UInt256.ofNat 1 * x = x := by
  apply Word.word_ext
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  rw [word_toNat_mul, Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256),
    Nat.one_mul, Nat.mod_eq_of_lt hx]

private theorem ofNat_zero_mul_toNat (x : UInt256) : (UInt256.ofNat 0 * x).toNat = 0 := by
  rw [word_toNat_mul, Word.word_toNat_ofNat]
  simp

theorem eq32_one (input : ByteArray) (hb : baseSize input = 32) :
    UInt256.eq (UInt256.ofNat 32) (MachineState.readWord input 0) = UInt256.ofNat 1 := by
  have hw : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  rw [hw, hb]; decide

theorem eq32_zero (input : ByteArray) (hb : baseSize input ≠ 32) :
    UInt256.eq (UInt256.ofNat 32) (MachineState.readWord input 0) = UInt256.ofNat 0 := by
  have hw : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  have hlt : baseSize input < 2 ^ 256 := EarlyWordProgram.header_lt input 0
  rw [hw]
  unfold UInt256.eq
  rw [Word.word_toNat_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
  simp [Ne.symm hb]

/-- With a 32-byte base the merged test either enters the window core directly or, for
`exponent = modulus - 1`, falls through the base-size recheck to the join at 47. -/
def wideHandled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowTwentyOneGasRoute.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) (hb : baseSize input = 32)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State, Nonempty (GasSteps (withModulus template input [] (UInt256.ofNat 25)) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 745 = true := by
    rw [ec.code]; exact paths.routeJump
  have hgen : Decode.isValidJumpDest (context template input).executionEnv.code 101 = true := by
    rw [ec.code]; exact paths.genJump
  have hraw := FermatNext.run_merge (context template input) m e (shiftWord input :: [])
    (by simp) hjump
  have hmw : FermatNext.mergeWord (context template input).executionEnv.calldata m e =
      FermatNext.fermatDiff m e := by
    change UInt256.eq (UInt256.ofNat 32) (MachineState.readWord input 0) * FermatNext.fermatDiff m e = _
    rw [eq32_one input hb]
    exact ofNat_one_mul _
  rw [hmw] at hraw
  by_cases hs : (FermatNext.fermatDiff m e).toNat = 0
  · rw [if_pos hs] at hraw
    have mergeSteps : GasSteps (withModulus template input [] (UInt256.ofNat 25))
        (withModulus template input [] (UInt256.ofNat 39)) :=
      paths.merge.steps (ec.transfer rfl rfl) rfl hraw
    have hrc := FermatNext.run_recheck (context template input) (m :: coreStack input [])
      (by simp [coreStack]) hgen
    have hx : (UInt256.xor (UInt256.ofNat 32)
        (MachineState.readWord (context template input).executionEnv.calldata 0)).toNat = 0 := by
      change (UInt256.xor (UInt256.ofNat 32) (MachineState.readWord input 0)).toNat = 0
      exact (EarlyWordProgram.baseDiff_zero_iff input).mpr hb
    rw [if_pos hx] at hrc
    have recheckSteps : GasSteps (withModulus template input [] (UInt256.ofNat 39))
        (joinState template input []) :=
      paths.recheck.steps (ec.transfer rfl rfl) rfl hrc
    obtain ⟨final, ⟨tail⟩, done, result⟩ :=
      handled paths legacy template env hcall input [] (by simp) hmatch hbn hsecp
    exact ⟨final, ⟨(mergeSteps.trans recheckSteps).trans tail⟩, done, result⟩
  · rw [if_neg hs] at hraw
    have mergeSteps : GasSteps (withModulus template input [] (UInt256.ofNat 25))
        (WindowTwentyOneGasRoute.entryState template input []) :=
      paths.merge.steps (ec.transfer rfl rfl) rfl hraw
    obtain ⟨oldFinal, ⟨oldTrace⟩, oldDone, oldResult⟩ :=
      WindowTwentyOneGasRoute.handled legacy template env hcall input [] (by simp) hmatch
    exact ⟨oldFinal, ⟨mergeSteps.trans oldTrace⟩, oldDone, oldResult⟩

/-- Any other base size: the loads at 16 read garbage words, the merged test is zero, and the
recheck at 39 leaves for the general-width entry at 101 with those three words on the stack. -/
def missSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input ≠ 32) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 16) [])
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 101)
        [MachineState.readWord input 160, MachineState.readWord input 128,
          MachineState.readWord input 96]) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 745 = true := by
    rw [ec.code]; exact paths.routeJump
  have hgen : Decode.isValidJumpDest (context template input).executionEnv.code 101 = true := by
    rw [ec.code]; exact paths.genJump
  have hf := FermatNext.run_fast (context template input) [] (by simp)
  have fastSteps : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 16) [])
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 25)
        [MachineState.readWord input 160, MachineState.readWord input 128,
          MachineState.readWord input 96]) :=
    paths.fast.steps (ec.transfer rfl rfl) rfl hf
  have hraw := FermatNext.run_merge (context template input) (MachineState.readWord input 160)
    (MachineState.readWord input 128) [MachineState.readWord input 96] (by simp) hjump
  have hz : (FermatNext.mergeWord (context template input).executionEnv.calldata
      (MachineState.readWord input 160) (MachineState.readWord input 128)).toNat = 0 := by
    change (UInt256.eq (UInt256.ofNat 32) (MachineState.readWord input 0) *
      FermatNext.fermatDiff (MachineState.readWord input 160) (MachineState.readWord input 128)).toNat = 0
    rw [eq32_zero input hb]
    exact ofNat_zero_mul_toNat _
  rw [if_pos hz] at hraw
  have mergeSteps := paths.merge.steps (ec.transfer (t := WindowTwentyOneEntry.framed
      (context template input) (UInt256.ofNat 25) [MachineState.readWord input 160,
        MachineState.readWord input 128, MachineState.readWord input 96]) rfl rfl) rfl hraw
  have hrc := FermatNext.run_recheck (context template input)
    [MachineState.readWord input 160, MachineState.readWord input 128, MachineState.readWord input 96]
    (by simp) hgen
  have hx : ¬ (UInt256.xor (UInt256.ofNat 32)
      (MachineState.readWord (context template input).executionEnv.calldata 0)).toNat = 0 := by
    change ¬ (UInt256.xor (UInt256.ofNat 32) (MachineState.readWord input 0)).toNat = 0
    exact fun h => hb ((EarlyWordProgram.baseDiff_zero_iff input).mp h)
  rw [if_neg hx] at hrc
  have recheckSteps := paths.recheck.steps (ec.transfer (t := WindowTwentyOneEntry.framed
      (context template input) (UInt256.ofNat 39) [MachineState.readWord input 160,
        MachineState.readWord input 128, MachineState.readWord input 96]) rfl rfl) rfl hrc
  exact (fastSteps.trans mergeSteps).trans recheckSteps

/-- The general-width entry at 101 with a base size up to 32 builds the join frame
with the base word shifted by `8 * (32 - baseSize)` and leaves `32 - baseSize` under it. -/
def genSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input ≤ 32) (rest : List UInt256) (hrest : rest.length ≤ 980) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 101) rest)
      (joinState template input (UInt256.ofNat (32 - baseSize input) :: rest)) := by
  let ec := WindowTwentyOneGasRoute.context_env template env input
  have h238 : Decode.isValidJumpDest (context template input).executionEnv.code 219 = true := by
    rw [ec.code]
    exact paths.bigJump
  have h31 : Decode.isValidJumpDest (context template input).executionEnv.code 47 = true := by
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
  have hbw : UInt256.shiftRight (MachineState.readWord (context template input).executionEnv.calldata 96)
      (UInt256.ofNat ((32 - baseSize input) * 8)) = shiftWord input := rfl
  rw [hbw] at hl
  have gc : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 101) rest)
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 112)
        (UInt256.ofNat (baseSize input) :: UInt256.ofNat 32 :: rest)) :=
    paths.genCheck.steps (ec.transfer rfl rfl) rfl hc
  have gl : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 112)
        (UInt256.ofNat (baseSize input) :: UInt256.ofNat 32 :: rest))
      (joinState template input (UInt256.ofNat (32 - baseSize input) :: rest)) :=
    paths.genLoad.steps (ec.transfer rfl rfl) rfl hl
  exact gc.trans gl

end CycleSubmission.Global.FermatGas
