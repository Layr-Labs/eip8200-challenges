import Challenge.Modexp.Submission.Proofs.Fast.SquareRow
import Challenge.Modexp.Submission.Proofs.Fast.SquareCaches

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
Row bookkeeping used by the square-loop caller and its mathematical invariant.
`TnM128SquareFullSteps` supplies the concrete eight-limb execution trace.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareRows

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareModel SquareResult SquareRow CiosCached
open CiosCachedMidMemory CarryRowModel StagedOperand

/-! ## Row bookkeeping -/

/-- Entry retained by setup: 3562 for eight limbs, 5309 for four limbs.
Eight-limb square rows advance this slot by 37. Four-limb squares use the
separate R4 routine and retain their initial slot throughout the call. -/
def sqEnt (n i : Nat) : Nat := 3562 + 1747 * ((8 - n) / 4) + 37 * i

/-- Frame slot 14 at row head `i`: the row-0 value `a0` (the setup's `aEnd`, or zero when
the in-kernel loop re-enters), and the limb `x_{i-1}` that row `i - 1` parked there. -/
def sqPrev (a0 : UInt256) (M0 : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => a0
  | i + 1 => sqX (sqRowsCarry M0 n i) n i

/-- Any row-0 slot 14 with a clear top bit gives the row-0 carry `tb = 0`: the setup's
`&a_{n-1} < 2 ^ 255` and the loop's zero both qualify. -/
theorem sgt_zero_setup (n : Nat) (hn : n ≤ 8) :
    UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat (512 + 32 * n - 32)) = UInt256.ofNat 0 := by
  apply sgt_zero_eq_zero_of_lt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sgt_zero_zero : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  decide

/-- Slot 14 when the rows are done: the limb the last row parked there. -/
def sqLast (M0 : ByteArray) (n : Nat) : UInt256 := sqX (sqRowsCarry M0 n (n - 1)) n (n - 1)

theorem sqTb_eq_prev (a0 : UInt256) (M0 : ByteArray) (n i : Nat) (hi : i < n) (hn : n ≤ 8)
    (ha0 : UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0) :
    UInt256.sgt (UInt256.ofNat 0) (sqPrev a0 M0 n i) = sqTb (sqRowsCarry M0 n i) n i := by
  cases i with
  | zero =>
      show UInt256.sgt (UInt256.ofNat 0) a0 = UInt256.ofNat 0
      exact ha0
  | succ j => exact (sqTb_succ_carry M0 n j (by omega) hn).symm

def rowState (s : State) (a0 : UInt256) (M0 : ByteArray) (n : Nat)
    (tl inv m0 m96 m64 m32 pdst ret : UInt256) (rest : List UInt256) (i : Nat) : State :=
  outState s (sqRowsCarry M0 n i) 2368 n i (UInt256.ofNat 4258) (UInt256.ofNat (sqEnt n i)) inv m0
    (tl :: m96 :: m64 :: m32 :: sqPrev a0 M0 n i :: pdst :: ret :: rest)

theorem sqEnt_succ (n i : Nat) : sqEnt n i + 37 = sqEnt n (i + 1) := by
  unfold sqEnt; omega


end Challenge.Modexp.Submission.Proofs.Fast.SquareRows
