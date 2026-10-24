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

def sqEnt (n i : Nat) : Nat := 3347 + 1769 * ((8 - n) / 4) + 37 * i

def sqPrev (a0 : UInt256) (M0 : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => a0
  | i + 1 => sqX (sqRowsCarry M0 n i) n i

theorem sgt_zero_setup (n : Nat) (hn : n ≤ 8) :
    UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat (512 + 32 * n - 32)) = UInt256.ofNat 0 := by
  apply sgt_zero_eq_zero_of_lt
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem sgt_zero_zero : UInt256.sgt (UInt256.ofNat 0) (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  decide

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
  outState s (sqRowsCarry M0 n i) 2368 n i (UInt256.ofNat 5297) (UInt256.ofNat (sqEnt n i)) m32 m64 m0
    (tl :: m96 :: inv :: UInt256.ofNat 0 :: sqPrev a0 M0 n i :: pdst :: ret :: rest)

theorem sqEnt_succ (n i : Nat) : sqEnt n i + 37 = sqEnt n (i + 1) := by
  unfold sqEnt; omega


end Challenge.Modexp.Submission.Proofs.Fast.SquareRows
