import Challenge.EvmProof.Word
import Mathlib.Tactic.IntervalCases

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollEntry
open EvmSemantics

def skipped (n : Nat) : Nat :=
  (UInt256.land (UInt256.ofNat 0 - UInt256.ofNat n) (UInt256.ofNat 3)).toNat

def cellIndex (n j : Nat) : Nat := (skipped n + j) % 4

def entryWord (n : Nat) : UInt256 :=
  UInt256.ofNat 3684 + UInt256.ofNat 39 *
    UInt256.land (UInt256.ofNat 0 - UInt256.ofNat n) (UInt256.ofNat 3)

theorem index_lt (n j : Nat) : cellIndex n j < 4 := Nat.mod_lt _ (by decide)

theorem index_succ (n j : Nat) :
    cellIndex n (j + 1) = (cellIndex n j + 1) % 4 := by
  unfold cellIndex
  rw [← Nat.add_assoc, Nat.add_mod]

theorem index_next (n j : Nat) (h : cellIndex n j < 3) :
    cellIndex n (j + 1) = cellIndex n j + 1 := by
  rw [index_succ, Nat.mod_eq_of_lt (by omega)]

theorem index_wrap (n j : Nat) (h : cellIndex n j = 3) :
    cellIndex n (j + 1) = 0 := by
  rw [index_succ, h]

theorem index_last (n : Nat) (hn : 1 ≤ n) (hcap : n ≤ 32) :
    cellIndex n (n - 1) = 3 := by
  interval_cases n <;> decide

theorem entryWord_eq (n : Nat) (hn : 1 ≤ n) (hcap : n ≤ 32) :
    entryWord n = UInt256.ofNat (3684 + 39 * cellIndex n 0) := by
  interval_cases n <;> decide

#print axioms index_last
#print axioms entryWord_eq
end Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollEntry
