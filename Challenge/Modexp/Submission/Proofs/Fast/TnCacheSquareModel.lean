import Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowModel
import Challenge.Modexp.Submission.Proofs.Fast.SquareResult

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel SquareModel SquareResult TnCacheMemory TnCacheRowModel

def liftMac (q : MacState) (tn : UInt256) : MacState := ⟨lift q.memory tn,q.carry⟩

private theorem mac_ext {a b : MacState} (hm : a.memory = b.memory)
    (hc : a.carry = b.carry) : a = b := by
  cases a; cases b; cases hm; cases hc; rfl

theorem run_lift (q : MacState) (tn bi : UInt256) (pa n j0 k : Nat)
    (hpa : pa+32*n ≤ 2080 ∨ 2112 ≤ pa) (hk : j0+k ≤ n) :
    l1Run (liftMac q tn) bi pa n j0 k = liftMac (l1Run q bi pa n j0 k) tn := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have prev := ih (by omega)
      have hx := read_lift_outside (l1Run q bi pa n j0 k).memory tn
        (pa+32*(n-1-(j0+k))) (by omega)
      have ht := read_lift_outside (l1Run q bi pa n j0 k).memory tn
        (2112+32*(n-1-(j0+k))) (Or.inr (by omega))
      rw [l1Run_succ, l1Run_succ, prev]
      simp only [l1StepOn, liftMac, hx, ht]
      apply mac_ext
      · exact (lift_put _ _ _ _ (Or.inr (by omega))).symm
      · rfl

theorem x_lift (mem : ByteArray) (tn : UInt256) (n i : Nat) :
    sqX (lift mem tn) n i = sqX mem n i :=
  read_lift_outside _ _ _ (Or.inr (by unfold aAddr; omega))

theorem pro_lift (mem : ByteArray) (tn : UInt256) (n i : Nat) (tb : UInt256) :
    sqPro (lift mem tn) n i tb = liftMac (sqPro mem n i tb) tn := by
  have hx := x_lift mem tn n i
  have ht := read_lift_outside mem tn (tAddr n i) (Or.inr (by unfold tAddr; omega))
  simp only [sqPro, sqCarry, sqSum, hx, ht, liftMac]
  apply mac_ext
  · exact (lift_put _ _ _ _ (Or.inr (by unfold tAddr; omega))).symm
  · rfl

theorem squareL1_lift (mem : ByteArray) (tn : UInt256) (n i : Nat) (tb : UInt256)
    (hi : i < n) :
    sqL1 (lift mem tn) n i tb = liftMac (sqL1 mem n i tb) tn := by
  unfold sqL1
  rw [pro_lift, x_lift]
  exact run_lift _ _ _ _ _ _ _ (Or.inr (by decide)) (by omega)

theorem tb_lift (mem : ByteArray) (tn : UInt256) (n i : Nat) :
    sqTb (lift mem tn) n i = sqTb mem n i := by
  cases i with
  | zero => rfl
  | succ i =>
      simp only [sqTb, read_lift_outside mem tn (aAddr n i)
        (Or.inr (by unfold aAddr; omega))]

def fromL1 (q : MacState) (tn : UInt256) (n : Nat) : CacheState :=
  let t := tn+q.carry
  let r := l2Step q.memory (rowMu q.memory n) (rowC0 q.memory n) n (n-1)
  ⟨put r.memory (t+r.carry) 2112,
   UInt256.lt t q.carry + UInt256.lt (t+r.carry) r.carry⟩

theorem from_lift (q : MacState) (tn : UInt256) (n : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    rowFromCarry (liftMac q tn) n =
      lift (fromL1 q tn n).memory (fromL1 q tn n).tn := by
  have h2 := l2_lift q.memory (tn+q.carry)
    (rowMu q.memory n) (rowC0 q.memory n) n (n-1) hn8
  simp only [rowFromCarry, rowFromL2Carry, liftMac, middle_lift,
    mu_lift _ _ _ hn, c0_lift _ _ _ hn hn8, overflow_lift]
  change tailCarry (l2Step (lift q.memory (tn+q.carry))
    (rowMu q.memory n) (rowC0 q.memory n) n (n-1)).memory
    (l2Step (lift q.memory (tn+q.carry)) (rowMu q.memory n)
      (rowC0 q.memory n) n (n-1)).carry
    (UInt256.lt (tn+q.carry) q.carry) = _
  rw [h2.1, h2.2, tail_lift]
  rfl

def squareRow (z : CacheState) (n i : Nat) : CacheState :=
  fromL1 (sqL1 z.memory n i (sqTb z.memory n i)) z.tn n

def squareRows (z : CacheState) (n : Nat) : Nat → CacheState
  | 0 => z
  | i+1 => squareRow (squareRows z n i) n i

theorem squareRow_lift (z : CacheState) (n i : Nat)
    (hi : i < n) (hn8 : n ≤ 8) :
    sqRowCarry (lift z.memory z.tn) n i (sqTb (lift z.memory z.tn) n i) =
      lift (squareRow z n i).memory (squareRow z n i).tn := by
  simp only [sqRowCarry, tb_lift, squareL1_lift _ _ _ _ _ hi, squareRow]
  exact from_lift _ _ _ (by omega) hn8

theorem squareRows_lift (z : CacheState) (n i : Nat)
    (hi : i ≤ n) (hn8 : n ≤ 8) :
    sqRowsCarry (lift z.memory z.tn) n i =
      lift (squareRows z n i).memory (squareRows z n i).tn := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [sqRowsCarry, squareRows, ih (by omega)]
      exact squareRow_lift _ _ _ (by omega) hn8

#print axioms squareRow_lift
#print axioms squareRows_lift
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheSquareModel
