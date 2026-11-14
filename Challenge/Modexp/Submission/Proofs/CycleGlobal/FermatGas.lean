import Challenge.Modexp.Submission.Proofs.CycleGlobal.WindowDispatchCore
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
    (WindowTwentyOneInput.modulusWord input::coreStack input tail)
/-- The join point at 48 with the core frame. -/
def joinState (template : State) (input : ByteArray) (tail : List UInt256) : State :=
  withModulus template input tail (UInt256.ofNat 10888)
private def fermatHandled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State) (env : Environment artifact fork template)
    (hcall : template.callStack = []) (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime)
    (he : (FermatNext.fermatDiff (WindowTwentyOneInput.modulusWord input)
      (WindowTwentyOneInput.exponentWord input)).toNat = 0)
    (hprime : (FermatProgram.primeValue (WindowTwentyOneInput.modulusWord input)).toNat ≠ 0) :
    ∃ final : State,Nonempty (GasSteps (withModulus template input tail 10496) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowDispatchCore.context_env template env input
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
    rw [Word.ofNat_sub_ofNat hm1 m.val.isLt,Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have hb : m.toNat < 2^256 := m.val.isLt; omega)
  have hexponent : WindowTwentyOneInput.exponentValue input =
      WindowTwentyOneInput.modulusValue input - 1 := by
    have h := congrArg UInt256.toNat heq
    rw [hsub,WindowTwentyOneInput.exponentWord_toNat,hmNat] at h
    exact h.symm
  let final := WindowTwentyOneReturn.returned (context template input) (UInt256.ofNat 10504)
    (FermatMath.resultWord input) 0 (coreStack input tail)
  have hr := FermatProgram.run_return (context template input) m (shiftWord input)
    (coreStack input tail) (by simp [coreStack]; omega) rfl rfl
  change WindowTwentyOneMsize.runInstructionsX FermatProgram.returnProgram
    (withModulus template input tail (UInt256.ofNat 10496)) = some final at hr
  have resultSteps : GasSteps (withModulus template input tail (UInt256.ofNat 10496)) final :=
    WindowTwentyOneMsize.Block.stepsX paths.result (ec.transfer rfl rfl) rfl hr
  refine ⟨final,⟨resultSteps⟩,?_,?_⟩
  · change (true && template.callStack.isEmpty) = true
    rw [hcall]
    rfl
  · have h := WindowTwentyOneReturn.returned_result (context template input)
      (UInt256.ofNat 9878) (FermatMath.resultWord input) 0 (coreStack input tail)
    rw [← FermatMath.result_spec input hmatch hp hexponent] at h
    exact h
/-- Boundary facts choose an existing Fermat result or the complete window route. -/
def handledFrom {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowDispatchCore.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime)
    (start : State)
    (yes : (FermatNext.fermatDiff (WindowTwentyOneInput.modulusWord input)
      (WindowTwentyOneInput.exponentWord input)).toNat = 0 →
      GasSteps start (withModulus template input tail 10628))
    (no : (FermatNext.fermatDiff (WindowTwentyOneInput.modulusWord input)
      (WindowTwentyOneInput.exponentWord input)).toNat ≠ 0 →
      GasSteps start (WindowDispatchCore.entryState template input tail)) :
    ∃ final : State,Nonempty (GasSteps start final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowDispatchCore.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 946 = true := by
    rw [ec.code]; exact paths.routeJump
  have htailjump : Decode.isValidJumpDest (context template input).executionEnv.code 10495 = true := by
    rw [ec.code]; exact paths.tailJump
  have hprimejump : Decode.isValidJumpDest (context template input).executionEnv.code 10628 = true := by
    rw [ec.code]; exact paths.primeJump
  obtain ⟨oldFinal,⟨oldTrace⟩,oldDone,oldResult⟩ :=
    WindowDispatchCore.handled legacy template env hcall input tail htail hmatch
  by_cases hs : (FermatNext.fermatDiff m e).toNat = 0
  · have commonSteps := yes hs
    have hpraw := FermatNext.run_prime (context template input) m (coreStack input tail)
      (by simp [coreStack]; omega) htailjump
    by_cases hp : (FermatProgram.primeValue m).toNat = 0
    · rw [if_pos hp] at hpraw
      have primeSteps : GasSteps (withModulus template input tail 10628) (withModulus template input tail 10678) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have hjraw := FermatNext.run_jumpTail (context template input) (m::coreStack input tail)
        (by simp [coreStack]; omega) hjump
      have jumpSteps : GasSteps (withModulus template input tail 10678)
          (WindowDispatchCore.entryState template input tail) :=
        paths.jumpTail.steps (ec.transfer rfl rfl) rfl hjraw
      exact ⟨oldFinal,⟨((commonSteps.trans primeSteps).trans jumpSteps).trans oldTrace⟩,oldDone,oldResult⟩
    · rw [if_neg hp] at hpraw
      have primeSteps : GasSteps (withModulus template input tail 10628) (withModulus template input tail 10495) :=
        paths.prime.steps (ec.transfer rfl rfl) rfl hpraw
      have htraw := FermatNext.run_tail (context template input) m e (shiftWord input::tail)
        (by simp; omega)
      have tailSteps : GasSteps (withModulus template input tail 10495) (withModulus template input tail 10496) :=
        paths.tail.steps (ec.transfer rfl rfl) rfl htraw
      obtain ⟨final,⟨trace⟩,done,result⟩ :=
        fermatHandled paths template env hcall input tail htail hmatch hbn hsecp hs hp
      exact ⟨final,⟨((commonSteps.trans primeSteps).trans tailSteps).trans trace⟩,done,result⟩
  · exact ⟨oldFinal,⟨(no hs).trans oldTrace⟩,oldDone,oldResult⟩
def handled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowDispatchCore.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State,Nonempty (GasSteps (withModulus template input tail 10888) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowDispatchCore.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hj : Decode.isValidJumpDest (context template input).executionEnv.code 946 = true := by
    rw [ec.code]; exact paths.routeJump
  have hp : Decode.isValidJumpDest (context template input).executionEnv.code 10628 = true := by
    rw [ec.code]; exact paths.primeJump
  have hraw := FermatNext.run_join (context template input) m e (shiftWord input::tail)
    (by simp; omega) hj
  refine handledFrom paths legacy template env hcall input tail htail hmatch hbn hsecp
    (withModulus template input tail 10888) ?_ ?_
  · intro hs
    have hr := hraw
    rw [if_pos hs] at hr
    have first : GasSteps (withModulus template input tail 10888)
        (withModulus template input tail 10897) :=
      paths.join.steps (ec.transfer rfl rfl) rfl hr
    have hpr := FermatNext.run_toPrime (context template input) (m::coreStack input tail)
      (by simp [coreStack]; omega) hp
    exact first.trans (paths.toPrime.steps (ec.transfer rfl rfl) rfl hpr)
  · intro hs
    have hr := hraw
    rw [if_neg hs] at hr
    exact paths.join.steps (ec.transfer rfl rfl) rfl hr
def handledFast {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowDispatchCore.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (tail : List UInt256) (htail : tail.length ≤ 590)
    (hmatch : WindowTwentyOneInput.Matches input)
    (hhalf : (UInt256.shiftRight
      (WindowTwentyOneInput.modulusWord input-WindowTwentyOneInput.exponentWord input)
      (UInt256.ofNat 1)).toNat = 0)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State,Nonempty (GasSteps (withModulus template input tail 48) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowDispatchCore.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hj : Decode.isValidJumpDest (context template input).executionEnv.code 946 = true := by
    rw [ec.code]; exact paths.routeJump
  have hp : Decode.isValidJumpDest (context template input).executionEnv.code 10628 = true := by
    rw [ec.code]; exact paths.primeJump
  have hraw := FermatNext.run_fastJoin (context template input) m e (shiftWord input::tail)
    hhalf (by simp; omega) hj
  refine handledFrom paths legacy template env hcall input tail htail hmatch hbn hsecp
    (withModulus template input tail 48) ?_ ?_
  · intro hs
    have hr := hraw
    rw [if_pos hs] at hr
    have first : GasSteps (withModulus template input tail 48)
        (withModulus template input tail 56) :=
      paths.fastJoin.steps (ec.transfer rfl rfl) rfl hr
    have hpr := FermatNext.run_fastToPrime (context template input) (m::coreStack input tail)
      (by simp [coreStack]; omega) hp
    exact first.trans (paths.fastToPrime.steps (ec.transfer rfl rfl) rfl hpr)
  · intro hs
    have hr := hraw
    rw [if_neg hs] at hr
    exact paths.fastJoin.steps (ec.transfer rfl rfl) rfl hr
/-- The unaligned word at 1: for base and exponent sizes below `2^248` it is the base size
shifted left by eight bits. -/
theorem readWord1_toNat (input : ByteArray)
    (hb : baseSize input < 2 ^ 248) (he : exponentSize input < 2 ^ 248) :
    (MachineState.readWord input 1).toNat = baseSize input * 256 := by
  rw [Bytes.readWord_toNat]
  have hsplit := Bytes.bytesToNatPadded_add input 1 31 1
  have hbsplit := Bytes.bytesToNatPadded_add input 0 1 31
  have hesplit := Bytes.bytesToNatPadded_add input 32 1 31
  have hlow := Bytes.bytesToNatPadded_lt_pow input 33 31
  simp only [baseSize,exponentSize] at hb he ⊢
  norm_num at hsplit hbsplit hesplit hlow hb he ⊢
  rw [hbsplit] at hb ⊢
  rw [hesplit] at he
  rw [hsplit]
  have h31 : (2 : Nat) ^ 248 = 256 ^ 31 := by norm_num
  have hb0 : Precompile.bytesToNatPadded input 0 1 = 0 := by
    by_contra hne
    have hpos : 1 ≤ Precompile.bytesToNatPadded input 0 1 := Nat.one_le_iff_ne_zero.mpr hne
    have : 256 ^ 31 ≤ Precompile.bytesToNatPadded input 0 1 * 256 ^ 31 :=
      Nat.le_mul_of_pos_left _ hpos
    omega
  have he0 : Precompile.bytesToNatPadded input 32 1 = 0 := by
    by_contra hne
    have hpos : 1 ≤ Precompile.bytesToNatPadded input 32 1 := Nat.one_le_iff_ne_zero.mpr hne
    have : 256 ^ 31 ≤ Precompile.bytesToNatPadded input 32 1 * 256 ^ 31 :=
      Nat.le_mul_of_pos_left _ hpos
    omega
  rw [hb0,he0]
  ring
theorem mergeShift_toNat (input : ByteArray)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024) :
    (MachineState.readWord input 1 - UInt256.ofNat 8191).toNat =
      (2 ^ 256 + baseSize input * 256 - 8191) % 2 ^ 256 := by
  rw [Word.word_toNat_sub,readWord1_toNat input (by omega) (by omega),Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 8191 < 2 ^ 256)]
/-- Any valid base size other than 32 shifts by at least 256: the merged word vanishes. -/
theorem mergeWord_ne32 (input : ByteArray) (modulus exponent : UInt256)
    (hb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024) (h32 : baseSize input ≠ 32) :
    (FermatNext.mergeWord input modulus exponent).toNat = 0 := by
  have hs := mergeShift_toNat input hb he
  have hge : 256 ≤ (MachineState.readWord input 1 - UInt256.ofNat 8191).toNat := by
    rw [hs]
    rcases Nat.lt_or_gt_of_ne h32 with hlt | hgt
    · rw [Nat.mod_eq_of_lt (by omega)]
      have : (2 : Nat) ^ 256 ≥ 2 ^ 20 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
      omega
    · have hge2 : 2 ^ 256 + baseSize input * 256 - 8191 = 2 ^ 256 + (baseSize input * 256 - 8191) := by
        omega
      rw [hge2,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega)]
      omega
  unfold FermatNext.mergeWord UInt256.shiftRight
  rw [if_pos hge]
  rfl
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
    simp only [withModulus,coreStack,shiftWord,WindowTwentyOneInput.modulusWord,
      WindowTwentyOneInput.exponentWord,WindowTwentyOneInput.baseWord,hb,Nat.sub_self,
      Nat.zero_mul,hs]
    rfl
  rw [hj]
  exact paths.fast.steps ((WindowDispatchCore.context_env template env input).transfer rfl rfl)
    rfl hraw
private theorem word_toNat_mul (a b : UInt256) : (a * b).toNat = (a.toNat * b.toNat) % 2 ^ 256 := by
  change (a.val * b.val).val = _
  rw [Fin.val_mul]
  rfl
private theorem ofNat_one_mul (x : UInt256) : UInt256.ofNat 1 * x = x := by
  apply Word.word_ext
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  rw [word_toNat_mul,Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256),
    Nat.one_mul,Nat.mod_eq_of_lt hx]
private theorem ofNat_zero_mul_toNat (x : UInt256) : (UInt256.ofNat 0 * x).toNat = 0 := by
  rw [word_toNat_mul,Word.word_toNat_ofNat]
  simp
theorem eq32_one (input : ByteArray) (hb : baseSize input = 32) :
    UInt256.eq (UInt256.ofNat 32) (MachineState.readWord input 0) = UInt256.ofNat 1 := by
  have hw : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  rw [hw,hb]; decide
theorem eq32_zero (input : ByteArray) (hb : baseSize input ≠ 32) :
    UInt256.eq (UInt256.ofNat 32) (MachineState.readWord input 0) = UInt256.ofNat 0 := by
  have hw : MachineState.readWord input 0 = UInt256.ofNat (baseSize input) := rfl
  have hlt : baseSize input < 2 ^ 256 := EarlyWordProgram.header_lt input 0
  rw [hw]
  unfold UInt256.eq
  rw [Word.word_toNat_ofNat,Word.word_toNat_ofNat,Nat.mod_eq_of_lt hlt,
    Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
  simp [Ne.symm hb]
/-- With a 32-byte base the merged test either enters the window core directly or
falls through the base-size recheck to the join at 48. -/
def wideHandled {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (legacy : WindowDispatchCore.Paths artifact fork)
    (template : State) (env : Environment artifact fork template) (hcall : template.callStack = [])
    (input : ByteArray) (hmatch : WindowTwentyOneInput.Matches input) (hb : baseSize input = 32)
    (hbn : FermatProgram.bn.toNat.Prime) (hsecp : FermatProgram.secp.toNat.Prime) :
    ∃ final : State,Nonempty (GasSteps (withModulus template input [] (UInt256.ofNat 25)) final) ∧
      final.isDone = true ∧ final.toResult = .returned (spec input) := by
  let ec := WindowDispatchCore.context_env template env input
  let m := WindowTwentyOneInput.modulusWord input
  let e := WindowTwentyOneInput.exponentWord input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 946 = true := by
    rw [ec.code]; exact paths.routeJump
  have hgen : Decode.isValidJumpDest (context template input).executionEnv.code 96 = true := by
    rw [ec.code]; exact paths.genJump
  have hraw := FermatNext.run_merge (context template input) m e (shiftWord input::[])
    (by simp) hjump
  by_cases hs : (FermatNext.mergeWord (context template input).executionEnv.calldata m e).toNat = 0
  · rw [if_pos hs] at hraw
    have mergeSteps : GasSteps (withModulus template input [] (UInt256.ofNat 25))
        (withModulus template input [] (UInt256.ofNat 40)) :=
      paths.merge.steps (ec.transfer rfl rfl) rfl hraw
    have hrc := FermatNext.run_recheck (context template input) (m::coreStack input [])
      (by simp [coreStack]) hgen
    have hx : (UInt256.xor (UInt256.ofNat 32)
        (MachineState.readWord (context template input).executionEnv.calldata 0)).toNat = 0 := by
      change (UInt256.xor (UInt256.ofNat 32) (MachineState.readWord input 0)).toNat = 0
      exact (EarlyWordProgram.baseDiff_zero_iff input).mpr hb
    rw [if_pos hx] at hrc
    have recheckSteps : GasSteps (withModulus template input [] (UInt256.ofNat 40))
        (withModulus template input [] (UInt256.ofNat 48)) :=
      paths.recheck.steps (ec.transfer rfl rfl) rfl hrc
    have hptr : MachineState.readWord input 1 = UInt256.ofNat 8192 := by
      apply Word.word_ext
      rw [readWord1_toNat input (by rw [hb]; norm_num) (by rw [hmatch.2.1]; norm_num),hb]
      decide
    have hhalf : (UInt256.shiftRight (m-e) (UInt256.ofNat 1)).toNat = 0 := by
      change (FermatNext.mergeWord input m e).toNat = 0 at hs
      simpa only [FermatNext.mergeWord,hptr,
        show UInt256.ofNat 8192-UInt256.ofNat 8191 = UInt256.ofNat 1 by decide] using hs
    obtain ⟨final,⟨tail⟩,done,result⟩ :=
      handledFast paths legacy template env hcall input [] (by simp) hmatch hhalf hbn hsecp
    exact ⟨final,⟨(mergeSteps.trans recheckSteps).trans tail⟩,done,result⟩
  · rw [if_neg hs] at hraw
    have mergeSteps : GasSteps (withModulus template input [] (UInt256.ofNat 25))
        (WindowDispatchCore.entryState template input []) :=
      paths.merge.steps (ec.transfer rfl rfl) rfl hraw
    obtain ⟨oldFinal,⟨oldTrace⟩,oldDone,oldResult⟩ :=
      WindowDispatchCore.handled legacy template env hcall input [] (by simp) hmatch
    exact ⟨oldFinal,⟨mergeSteps.trans oldTrace⟩,oldDone,oldResult⟩
/-- Any other base size: the loads at 16 read garbage words, the merged test is zero, and the
recheck at 39 leaves for the general-width entry at 101 with those three words on the stack. -/
def missSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input ≠ 32) (hbb : baseSize input ≤ 1024) (he : exponentSize input ≤ 1024) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 16) [])
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 96)
        [MachineState.readWord input 160,MachineState.readWord input 128,
          MachineState.readWord input 96]) := by
  let ec := WindowDispatchCore.context_env template env input
  have hjump : Decode.isValidJumpDest (context template input).executionEnv.code 946 = true := by
    rw [ec.code]; exact paths.routeJump
  have hgen : Decode.isValidJumpDest (context template input).executionEnv.code 96 = true := by
    rw [ec.code]; exact paths.genJump
  have hf := FermatNext.run_fast (context template input) [] (by simp)
  have fastSteps : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 16) [])
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 25)
        [MachineState.readWord input 160,MachineState.readWord input 128,
          MachineState.readWord input 96]) :=
    paths.fast.steps (ec.transfer rfl rfl) rfl hf
  have hraw := FermatNext.run_merge (context template input) (MachineState.readWord input 160)
    (MachineState.readWord input 128) [MachineState.readWord input 96] (by simp) hjump
  have hz : (FermatNext.mergeWord (context template input).executionEnv.calldata
      (MachineState.readWord input 160) (MachineState.readWord input 128)).toNat = 0 :=
    mergeWord_ne32 input _ _ hbb he hb
  rw [if_pos hz] at hraw
  have mergeSteps := paths.merge.steps (ec.transfer (t := WindowTwentyOneEntry.framed
      (context template input) (UInt256.ofNat 25) [MachineState.readWord input 160,
        MachineState.readWord input 128,MachineState.readWord input 96]) rfl rfl) rfl hraw
  have hrc := FermatNext.run_recheck (context template input)
    [MachineState.readWord input 160,MachineState.readWord input 128,MachineState.readWord input 96]
    (by simp) hgen
  have hx : ¬ (UInt256.xor (UInt256.ofNat 32)
      (MachineState.readWord (context template input).executionEnv.calldata 0)).toNat = 0 := by
    change ¬ (UInt256.xor (UInt256.ofNat 32) (MachineState.readWord input 0)).toNat = 0
    exact fun h => hb ((EarlyWordProgram.baseDiff_zero_iff input).mp h)
  rw [if_neg hx] at hrc
  have recheckSteps := paths.recheck.steps (ec.transfer (t := WindowTwentyOneEntry.framed
      (context template input) (UInt256.ofNat 40) [MachineState.readWord input 160,
        MachineState.readWord input 128,MachineState.readWord input 96]) rfl rfl) rfl hrc
  exact (fastSteps.trans mergeSteps).trans recheckSteps
/-- The general-width entry at 101 with a base size up to 32 builds the join frame
with the base word shifted by `8 * (32 - baseSize)` and leaves `32 - baseSize` under it. -/
def genSteps {artifact : ProgramArtifact} {fork : Fork}
    (paths : FermatNext.Paths artifact fork) (template : State)
    (env : Environment artifact fork template) (input : ByteArray)
    (hb : baseSize input ≤ 32) (rest : List UInt256) (hrest : rest.length ≤ 980) :
    GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 96) rest)
      (joinState template input (UInt256.ofNat (32 - baseSize input)::rest)) := by
  let ec := WindowDispatchCore.context_env template env input
  have h238 : Decode.isValidJumpDest (context template input).executionEnv.code 207 = true := by
    rw [ec.code]
    exact paths.bigJump
  have h31 : Decode.isValidJumpDest (context template input).executionEnv.code 10888 = true := by
    rw [ec.code]
    exact paths.joinJump
  have hword : MachineState.readWord (context template input).executionEnv.calldata 0 =
      UInt256.ofNat (baseSize input) := rfl
  have hbig : baseSize input < 2 ^ 256 := by omega
  have hgt : (UInt256.gt (UInt256.ofNat (baseSize input)) (UInt256.ofNat 32)).toNat = 0 := by
    unfold UInt256.gt
    rw [Word.word_toNat_ofNat,Word.word_toNat_ofNat,Nat.mod_eq_of_lt hbig,
      Nat.mod_eq_of_lt (by norm_num : 32 < 2 ^ 256)]
    simp [Nat.not_lt.mpr hb]
  have hc := FermatNext.run_gen_check (context template input) rest (by omega) h238
  rw [hword,if_pos hgt] at hc
  have hl := FermatNext.run_gen_load (context template input) (UInt256.ofNat (baseSize input)) rest
    (by omega) h31
  have hsub := Word.ofNat_sub_ofNat hb (by decide : 32 < 2 ^ 256)
  have hshift : UInt256.shiftLeft (UInt256.ofNat 32 - UInt256.ofNat (baseSize input))
      (UInt256.ofNat 3) = UInt256.ofNat ((32 - baseSize input) * 8) := by
    rw [hsub,Word.shiftLeft_ofNat (by omega) (by decide) (by omega)]
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
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have hen : (UInt256.ofNat (96 + baseSize input)).toNat = 96 + baseSize input := by
    rw [Word.word_toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [hshift,hsub,hm160,he128,hmn,hen] at hl
  have hbw : UInt256.shiftRight (MachineState.readWord (context template input).executionEnv.calldata 96)
      (UInt256.ofNat ((32 - baseSize input) * 8)) = shiftWord input := rfl
  rw [hbw] at hl
  have gc : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 96) rest)
      (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 107)
        (UInt256.ofNat (baseSize input)::UInt256.ofNat 32::rest)) :=
    paths.genCheck.steps (ec.transfer rfl rfl) rfl hc
  have gl : GasSteps (WindowTwentyOneEntry.framed (context template input) (UInt256.ofNat 107)
        (UInt256.ofNat (baseSize input)::UInt256.ofNat 32::rest))
      (joinState template input (UInt256.ofNat (32 - baseSize input)::rest)) :=
    paths.genLoad.steps (ec.transfer rfl rfl) rfl hl
  exact gc.trans gl
end CycleSubmission.Global.FermatGas
