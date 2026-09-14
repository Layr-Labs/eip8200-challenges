import Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
import Challenge.Modexp.Submission.Proofs.Fast.CarryRowModel

set_option warningAsError false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowModel
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro CarryRowModel TnCacheMemory

structure CacheState where
  memory : ByteArray
  tn : UInt256

def row (z : CacheState) (pa pb n i : Nat) : CacheState :=
  let q := l1Step z.memory (rowBi z.memory pb n i) pa n n
  let t := z.tn + q.carry
  let r := l2Step q.memory (rowMu q.memory n) (rowC0 q.memory n) n (n-1)
  ⟨put r.memory (t+r.carry) 2112,
   UInt256.lt t q.carry + UInt256.lt (t+r.carry) r.carry⟩

def rows (z : CacheState) (pa pb n : Nat) : Nat → CacheState
  | 0 => z
  | i+1 => row (rows z pa pb n i) pa pb n i

theorem l1_lift (mem : ByteArray) (tn bi : UInt256) (pa n j : Nat)
    (hpa : pa+32*n ≤ 2080 ∨ 2112 ≤ pa) (hj : j ≤ n) :
    (l1Step (lift mem tn) bi pa n j).memory =
        lift (l1Step mem bi pa n j).memory tn ∧
      (l1Step (lift mem tn) bi pa n j).carry =
        (l1Step mem bi pa n j).carry := by
  induction j with
  | zero => exact ⟨rfl,rfl⟩
  | succ j ih =>
      have prev := ih (by omega)
      have hx := read_lift_outside (l1Step mem bi pa n j).memory tn
        (pa+32*(n-1-j)) (by omega)
      have ht := read_lift_outside (l1Step mem bi pa n j).memory tn
        (2112+32*(n-1-j)) (Or.inr (by omega))
      simp only [l1Step, prev.1, prev.2, hx, ht]
      exact ⟨(lift_put _ _ _ _ (Or.inr (by omega))).symm, True.intro⟩

theorem l2_lift (mem : ByteArray) (tn mu c0 : UInt256) (n k : Nat)
    (hn : n ≤ 8) :
    (l2Step (lift mem tn) mu c0 n k).memory =
        lift (l2Step mem mu c0 n k).memory tn ∧
      (l2Step (lift mem tn) mu c0 n k).carry =
        (l2Step mem mu c0 n k).carry := by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
      have hx := read_lift_outside (l2Step mem mu c0 n k).memory tn
        (32*(n-2-k)) (Or.inl (by omega))
      have ht := read_lift_outside (l2Step mem mu c0 n k).memory tn
        (2112+32*(n-2-k)) (Or.inr (by omega))
      simp only [l2Step, ih.1, ih.2, hx, ht]
      exact ⟨(lift_put _ _ _ _ (Or.inr (by omega))).symm, True.intro⟩

theorem mu_lift (mem : ByteArray) (tn : UInt256) (n : Nat) (hn : 1 ≤ n) :
    rowMu (lift mem tn) n = rowMu mem n := by
  unfold rowMu
  rw [read_lift_outside _ _ 2720 (Or.inr (by decide)),
      read_lift_outside _ _ (2080+32*n) (Or.inr (by omega))]

theorem c0_lift (mem : ByteArray) (tn : UInt256) (n : Nat)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    rowC0 (lift mem tn) n = rowC0 mem n := by
  unfold rowC0
  rw [read_lift_outside _ _ (32*n-32) (Or.inl (by omega)), mu_lift _ _ _ hn]

theorem bi_lift (mem : ByteArray) (tn : UInt256) (pb n i : Nat)
    (hpb : pb+32*n ≤ 2080 ∨ 2112 ≤ pb) (hn : 1 ≤ n) :
    rowBi (lift mem tn) pb n i = rowBi mem pb n i := by
  unfold rowBi
  exact read_lift_outside _ _ _ (by omega)

theorem middle_lift (mem : ByteArray) (tn c : UInt256) :
    midMem1 (lift mem tn) c = lift mem (tn+c) := by
  simp only [midMem1, read_lift]
  exact lift_overwrite mem tn (tn+c)

theorem overflow_lift (mem : ByteArray) (tn c : UInt256) :
    overflow (lift mem tn) c = UInt256.lt (tn+c) c := by
  simp only [overflow, read_lift]

theorem tail_lift (mem : ByteArray) (tn c f : UInt256) :
    tailCarry (lift mem tn) c f =
      lift (put mem (tn+c) 2112) (f+UInt256.lt (tn+c) c) := by
  simp only [tailCarry, tailMem1, read_lift]
  change lift (put (lift mem tn) (tn+c) 2112)
    (f+UInt256.lt (tn+c) c) = _
  rw [← lift_put mem tn (tn+c) 2112 (Or.inr (by decide)), lift_overwrite]

theorem row_lift (z : CacheState) (pa pb n i : Nat)
    (hpa : pa+32*n ≤ 2080 ∨ 2112 ≤ pa)
    (hpb : pb+32*n ≤ 2080 ∨ 2112 ≤ pb)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    rowCarry (lift z.memory z.tn) pa pb n i =
      lift (row z pa pb n i).memory (row z pa pb n i).tn := by
  have h1 := l1_lift z.memory z.tn (rowBi z.memory pb n i) pa n n hpa le_rfl
  let q := l1Step z.memory (rowBi z.memory pb n i) pa n n
  have h2 := l2_lift q.memory (z.tn+q.carry)
    (rowMu q.memory n) (rowC0 q.memory n) n (n-1) hn8
  simp only [rowCarry, rowL2Carry, rowL1, row, bi_lift _ _ _ _ _ hpb hn,
    h1.1, h1.2, middle_lift, mu_lift _ _ _ hn, c0_lift _ _ _ hn hn8,
    overflow_lift]
  change tailCarry (l2Step (lift q.memory (z.tn+q.carry))
    (rowMu q.memory n) (rowC0 q.memory n) n (n-1)).memory
    (l2Step (lift q.memory (z.tn+q.carry)) (rowMu q.memory n)
      (rowC0 q.memory n) n (n-1)).carry
    (UInt256.lt (z.tn+q.carry) q.carry) = _
  rw [h2.1, h2.2, tail_lift]

theorem rows_lift (z : CacheState) (pa pb n i : Nat)
    (hpa : pa+32*n ≤ 2080 ∨ 2112 ≤ pa)
    (hpb : pb+32*n ≤ 2080 ∨ 2112 ≤ pb)
    (hn : 1 ≤ n) (hn8 : n ≤ 8) :
    rowsCarry (lift z.memory z.tn) pa pb n i =
      lift (rows z pa pb n i).memory (rows z pa pb n i).tn := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp only [rowsCarry, rows, ih]
      exact row_lift _ pa pb n i hpa hpb hn hn8

#print axioms row_lift
#print axioms rows_lift
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheRowModel
