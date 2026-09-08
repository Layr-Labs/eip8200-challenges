import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineTail

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

def iterationProgram : List Instr :=
  [.op .JUMPDEST] ++ WindowNineBody.program ++ WindowNineTail.program (UInt256.ofNat 2821)

def repeatProgram : Nat → List Instr
  | 0 => []
  | count + 1 => repeatProgram count ++ iterationProgram

def loopState (template : State) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowNineGroup.state template (UInt256.ofNat 2821) base modulus
    (WindowNineMath.accumulator base modulus exponent.toNat (9 * count))
    (UInt256.shiftLeft exponent (UInt256.ofNat (4 * (1 + 9 * count))))
    (UInt256.ofNat (6 - count)) 0 rest

/-- The final decrement wraps, but no instruction reads this dead counter again. -/
def finishState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowNineGroup.state template (UInt256.ofNat 3028) base modulus
    (WindowNineMath.accumulator base modulus exponent.toNat 63)
    (UInt256.shiftLeft
      (UInt256.shiftLeft exponent (UInt256.ofNat 220)) (UInt256.ofNat 36))
    (UInt256.ofNat 0 - UInt256.ofNat 1) 0 rest

private theorem advancePC_ofNat (count pc : Nat) :
    advancePC count (UInt256.ofNat pc) = UInt256.ofNat (pc + count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [advancePC, ih, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_continue (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count < 6)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2821 = true) :
    runInstructions iterationProgram (loopState template base modulus exponent count rest) =
    some (loopState template base modulus exponent (count + 1) rest) := by
  let a := WindowNineMath.accumulator base modulus exponent.toNat (9 * count)
  let e := UInt256.shiftLeft exponent (UInt256.ofNat (4 * (1 + 9 * count)))
  let c := UInt256.ofNat (6 - count)
  let nextA := WindowNineMath.accumulator base modulus exponent.toNat (9 * (count + 1))
  have ha : WindowNineMath.advance base modulus exponent.toNat (1 + 9 * count) 9 a = nextA := by
    dsimp only [a, nextA]
    rw [show 9 * (count + 1) = 9 * count + 9 by omega, WindowNineMath.accumulator_nine]
  have hc : UInt256.isTrue c := by
    change (6 - count) % (2 ^ 256) ≠ 0
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hsub : c - UInt256.ofNat 1 = UInt256.ofNat (6 - (count + 1)) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  have hshift : UInt256.shiftLeft e (UInt256.ofNat 36) =
      UInt256.shiftLeft exponent (UInt256.ofNat (4 * (1 + 9 * (count + 1)))) := by
    rw [WindowNineTail.shift_nine exponent (1 + 9 * count) (by omega)]
    congr 2
  have hh := WindowNineTail.run_head template (UInt256.ofNat 2821)
    base modulus a e c rest hrest
  have hb := WindowNineBody.run_nine template (UInt256.ofNat 2822)
    base modulus a exponent c (1 + 9 * count) (by omega) rest hrest
  have ht := WindowNineTail.run_tail template (UInt256.ofNat 3014) (UInt256.ofNat 2821)
    base modulus nextA e c rest hrest hjump
  rw [ha, advancePC_ofNat] at hb
  rw [if_pos hc, hsub, hshift] at ht
  have hhb := runInstructions_append_some _ _ _ _ _ hh hb
  have hall := runInstructions_append_some _ _ _ _ _ hhb ht
  simpa only [iterationProgram, loopState, a, e, c, nextA] using hall

theorem run_last (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2821 = true) :
    runInstructions iterationProgram (loopState template base modulus exponent 6 rest) =
    some (finishState template base modulus exponent rest) := by
  let a := WindowNineMath.accumulator base modulus exponent.toNat 54
  let e := UInt256.shiftLeft exponent (UInt256.ofNat 220)
  let nextA := WindowNineMath.accumulator base modulus exponent.toNat 63
  have ha : WindowNineMath.advance base modulus exponent.toNat 55 9 a = nextA := by
    exact (WindowNineMath.accumulator_nine base modulus exponent.toNat 54).symm
  have hh := WindowNineTail.run_head template (UInt256.ofNat 2821)
    base modulus a e (UInt256.ofNat 0) rest hrest
  have hb := WindowNineBody.run_nine template (UInt256.ofNat 2822)
    base modulus a exponent (UInt256.ofNat 0) 55 (by decide) rest hrest
  have ht := WindowNineTail.run_tail template (UInt256.ofNat 3014) (UInt256.ofNat 2821)
    base modulus nextA e (UInt256.ofNat 0) rest hrest hjump
  rw [ha, advancePC_ofNat] at hb
  rw [if_neg (by decide : ¬ UInt256.isTrue (UInt256.ofNat 0)), advancePC_ofNat] at ht
  have hhb := runInstructions_append_some _ _ _ _ _ hh hb
  have hall := runInstructions_append_some _ _ _ _ _ hhb ht
  simpa only [iterationProgram, loopState, finishState, a, e, nextA] using hall

theorem run_prefix (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count ≤ 6)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2821 = true) :
    runInstructions (repeatProgram count) (loopState template base modulus exponent 0 rest) =
    some (loopState template base modulus exponent count rest) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      exact runInstructions_append_some _ _ _ _ _ (ih (by omega))
        (run_continue template base modulus exponent count (by omega) rest hrest hjump)

/-- Exactly seven passes process the remaining sixty-three exponent nibbles. -/
theorem run_seven (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2821 = true) :
    runInstructions (repeatProgram 7) (loopState template base modulus exponent 0 rest) =
    some (finishState template base modulus exponent rest) := by
  exact runInstructions_append_some _ _ _ _ _
    (run_prefix template base modulus exponent 6 (by decide) rest hrest hjump)
    (run_last template base modulus exponent rest hrest hjump)

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNineLoop
