import Challenge.Modexp.Submission.Proofs.CycleGlobal.LazyTopMemory
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.LazyTopStep
open EvmSemantics
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open LazyTopMemory
def raw (mem : ByteArray) (n : Nat) : ByteArray :=
  (Shift.macOf (Shift.uMem mem n) n (Shift.qhatOf (Shift.uMem mem n))).memory
def next (mem : ByteArray) (n mm : Nat) : ByteArray :=
  let um := Shift.uMem mem n
  let q := Shift.qhatOf um
  let mac := Shift.macOf um n q
  if Shift.negOf mac.memory mac.carry q = UInt256.ofNat 0 then mac.memory
  else Shift.stepMem mem n mm
theorem next_zero (mem : ByteArray) (n mm : Nat)
    (h : Shift.negOf (raw mem n)
      (Shift.macOf (Shift.uMem mem n) n (Shift.qhatOf (Shift.uMem mem n))).carry
      (Shift.qhatOf (Shift.uMem mem n)) = UInt256.ofNat 0) :
    next mem n mm = raw mem n := by
  dsimp only [next]
  exact if_pos h
theorem next_nonzero (mem : ByteArray) (n mm : Nat)
    (h : Shift.negOf (raw mem n)
      (Shift.macOf (Shift.uMem mem n) n (Shift.qhatOf (Shift.uMem mem n))).carry
      (Shift.qhatOf (Shift.uMem mem n)) ≠ UInt256.ofNat 0) :
    next mem n mm = Shift.stepMem mem n mm := by
  dsimp only [next]
  exact if_neg h
theorem raw_size (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) :
    2112 ≤ (raw mem n).size := by
  unfold raw Shift.macOf
  exact le_trans (uMem_size mem n hn) (l1_size _ _ _ _ _)
theorem next_eq {a b : ByteArray} (h : Related a b) (n mm : Nat) (hn : 1 ≤ n) :
    next a n mm = next b n mm := by
  unfold next
  rw [uMem_eq h n hn,stepMem_eq h n mm hn]
theorem related (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n)
    (hfix : Shift.negOf (raw mem n)
        (Shift.macOf (Shift.uMem mem n) n (Shift.qhatOf (Shift.uMem mem n))).carry
        (Shift.qhatOf (Shift.uMem mem n)) = UInt256.ofNat 0 →
      Shift.stepMem mem n mm =
        Exp.storeWord (raw mem n) 2080 (UInt256.ofNat 0)) :
    Related (next mem n mm) (Shift.stepMem mem n mm) := by
  dsimp only [next]
  split
  · next h =>
      change Related (raw mem n) (Shift.stepMem mem n mm)
      rw [hfix h]
      exact store_related _ _ (raw_size mem n hn)
  · exact ⟨TnCacheMemory.refl _,rfl⟩
def iter (mem : ByteArray) (n mm : Nat) : Nat → ByteArray
  | 0 => mem
  | k+1 => next (iter mem n mm k) n mm
theorem iter_related (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n)
    (hstep : ∀ i,Related (next (Shift.stepMems mem n mm i) n mm)
      (Shift.stepMem (Shift.stepMems mem n mm i) n mm)) :
    ∀ k,Related (iter mem n mm k) (Shift.stepMems mem n mm k) := by
  intro k
  induction k with
  | zero => exact ⟨TnCacheMemory.refl _,rfl⟩
  | succ k ih =>
      change Related (next (iter mem n mm k) n mm)
        (Shift.stepMem (Shift.stepMems mem n mm k) n mm)
      rw [next_eq ih n mm hn]
      exact hstep k
theorem fix_zero (mem : ByteArray) (n mm : Nat)
    (htn : MachineState.readWord mem 2080 = UInt256.ofNat 0) :
    Shift.fixMem mem n mm (UInt256.ofNat 0) = mem := by
  have htv : Shift.tv mem n < Limbs.radix^n := by
    rw [Shift.tv_def,htn]
    simpa only [show (UInt256.ofNat 0).toNat = 0 by decide,
      Nat.zero_mul,Nat.zero_add] using Csub.lowValue_lt mem 2112 n n
  simp only [Shift.fixMem,Shift.addCount,
    show (UInt256.ofNat 0).toNat = 0 by decide,ite_true,
    Shift.addRounds,Shift.subCount,if_pos htv,Shift.subRounds]
theorem related_valid (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix^n)
    (htop : Limbs.radix^n < 2*mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem Shift.NEG n (Limbs.radix^n-mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : Shift.PreOK mem) :
    Related (next mem n mm) (Shift.stepMem mem n mm) := by
  apply related mem n mm (by omega)
  intro h0
  have htn := Shift.mid_neg_tn_zero mem n mm r hn hn32 hmpos hmm htop
    hmod hneg hbase hr hpre h0
  dsimp only [Shift.stepMem,Shift.midMem]
  rw [show Shift.negOf (Shift.macOf (Shift.uMem mem n) n (Shift.qhatOf (Shift.uMem mem n))).memory
    (Shift.macOf (Shift.uMem mem n) n (Shift.qhatOf (Shift.uMem mem n))).carry
    (Shift.qhatOf (Shift.uMem mem n)) = UInt256.ofNat 0 from h0,htn]
  apply fix_zero
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _
theorem iter_valid (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix^n)
    (htop : Limbs.radix^n < 2*mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem Shift.NEG n (Limbs.radix^n-mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : Shift.PreOK mem) :
    ∀ k,Related (iter mem n mm k) (Shift.stepMems mem n mm k) := by
  apply iter_related mem n mm (by omega)
  intro i
  apply related_valid (Shift.stepMems mem n mm i) n mm
    (r*Limbs.radix^i % mm) hn hn32 hmpos hmm htop
  · exact Shift.stepMems_modulus mem n mm (by omega) hn32 hmod i
  · exact Shift.stepMems_neg mem n mm (by omega) hn32 hneg i
  · exact Shift.stepMems_represents mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre i
  · exact Nat.mod_lt _ hmpos
  · exact Shift.PreOK_stepMems mem n mm (by omega) hn32 hpre i
#print axioms iter_valid
end CycleSubmission.Global.LazyTopStep
