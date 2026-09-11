import Challenge.Modexp.Submission.Proofs.Fast.ShiftTrace4

set_option warningAsError false
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000

/-!
# The shift loop and the whole hit path

`gasSteps_hitPath` runs from the dispatcher entry to `BDONE`; `gasSteps_missPath`
runs from the dispatcher entry to the old `r0` block.  The value facts the
exponent phase needs at `BDONE` are collected in `hitFacts`.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Shift

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Bytecode

/-! ## Value facts feeding the trace (proved in `ShiftModel`) -/

/-- The repair-loop facts of one step, from the step's arithmetic. -/
theorem repairFacts_of (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2048 n r) (hr : r < mm) :
    RepairFacts
      (midMem (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n)))
      n mm
      (negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry (qhatOf (uMem mem n))) :=
  (step_spec mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr).1

/-- The configuration words survive a step. -/
theorem frame_stepMem {mem : ByteArray} {n bsize mm minv : Nat} (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hf : Exp.Frame mem n bsize minv) : Exp.Frame (stepMem mem n mm) n bsize minv where
  s32 := by
    rw [stepMem_readWord_disjoint mem n mm 9344 hn
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]; exact hf.s32
  minvW := by
    rw [stepMem_readWord_disjoint mem n mm 9376 hn
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]; exact hf.minvW
  ml := by
    rw [stepMem_readWord_disjoint mem n mm 9408 hn
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]; exact hf.ml
  tl := by
    rw [stepMem_readWord_disjoint mem n mm 9440 hn
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]; exact hf.tl
  eoff := by
    rw [stepMem_readWord_disjoint mem n mm 9472 hn
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩]; exact hf.eoff

theorem stepInv_stepMem {mem : ByteArray} {n bsize mm minv : Nat} (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (inv : StepInv mem n bsize mm minv) : StepInv (stepMem mem n mm) n bsize mm minv where
  frame := frame_stepMem hn hn32 inv.frame
  modulus := fastRepresents_stepMem mem n mm 0 n mm hn
    ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩ inv.modulus
  neg := fastRepresents_stepMem mem n mm NEG n _ hn
    ⟨Or.inr (by unfold NEG; omega), Or.inl (by unfold NEG; omega), Or.inl (by unfold NEG; omega)⟩
    inv.neg

theorem stepInv_stepMems {mem : ByteArray} {n bsize mm minv : Nat} (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (inv : StepInv mem n bsize mm minv) :
    ∀ i, StepInv (stepMems mem n mm i) n bsize mm minv := by
  intro i
  induction i with
  | zero => exact inv
  | succ i ih => exact stepInv_stepMem hn hn32 ih

/-! ## The shift loop -/

def gasSteps_shiftLoop (s : State) (mem : ByteArray) (n bsize esize msize mm minv r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (e : Env s) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (inv : StepInv mem n bsize mm minv)
    (hbase : Model.FastRepresents mem 2048 n r) (hr : r < mm) :
    Challenge.EvmProof.GasSteps (shiftLoopState s mem n bsize esize msize n)
      (shiftLoopState s (stepMems mem n mm n) n bsize esize msize 0) :=
  Challenge.EvmProof.GasSteps.cast
    (Challenge.EvmProof.GasSteps.iterateBounded
      (I := fun i => shiftLoopState s (stepMems mem n mm i) n bsize esize msize (n - i)) n
      (fun i hi =>
        have invI := stepInv_stepMems (by omega) hn32 inv i
        have hbaseI := stepMems_represents mem n mm r hn hn32 hmpos hmm htop inv.modulus inv.neg
          hbase hr i
        Challenge.EvmProof.GasSteps.cast
          (gasSteps_step s (stepMems mem n mm i) n bsize esize msize (n - i) mm minv
            (by omega) (by omega) hn hn32 e invI
            (repairFacts_of (stepMems mem n mm i) n mm _ hn hn32 hmpos hmm htop invI.modulus
              invI.neg hbaseI (Nat.mod_lt _ hmpos)))
          rfl (by
            show shiftLoopState s (stepMem (stepMems mem n mm i) n mm) n bsize esize msize
              (n - i - 1) = shiftLoopState s (stepMems mem n mm (i + 1)) n bsize esize msize
              (n - (i + 1))
            rw [show n - i - 1 = n - (i + 1) from by omega]
            rfl)))
    (by simp [stepMems]) (by simp)

/-! ## The whole hit path -/

/-- Memory after the raw base has been reduced by the first `CSUB`. -/
def m1Of (mem input : ByteArray) (n : Nat) : ByteArray :=
  Csub.csResultMemory (hitMem mem input n) n 2048

/-- Memory at the shift loop entry. -/
def m2Of (mem input : ByteArray) (n : Nat) : ByteArray :=
  preMem (negStep (m1Of mem input n) n n).memory

/-- Memory at `BDONE`. -/
def hitFinalMem (mem input : ByteArray) (n mm : Nat) : ByteArray :=
  stepMems (m2Of mem input n) n mm n

/-- The base value the first `CSUB` leaves in `BASE`: `b mod m`. -/
theorem m1_base (mem input : ByteArray) (n mm : Nat) (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hmpos : 0 < mm) (hodd : mm % 2 = 1)
    (hmod : Model.FastRepresents mem 0 n mm) (htop : R1.TopBitSet mem) :
    Model.FastRepresents (m1Of mem input n) 2048 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
  have hts : Model.FastRepresents (hitMem mem input n) 8256 n
      (Precompile.bytesToNatPadded input 96 (32 * n)) := by
    unfold hitMem Exp.storeWord
    refine Model.fastRepresents_writeWord_disjoint _ 8224 8256 n _ _ (Or.inl (by omega)) ?_
    have hsource := Setup.fastRepresents_bytes input 96 n
    apply Model.fastRepresents_of_limbs hsource.1
    intro k hk
    rw [FullBase.readWord_copyFrom _ input 96 8256 (32 * n) (n - 1 - k) (by omega)]
    exact Model.readLimb_of_fastRepresents hsource hk
  have hmodH : Model.FastRepresents (hitMem mem input n) 0 n mm := by
    unfold hitMem Exp.storeWord
    refine Model.fastRepresents_writeWord_disjoint _ 8224 0 n _ _ (Or.inr (by omega)) ?_
    refine Model.fastRepresents_writeBytes_disjoint _ _ 8256 0 n _
      (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega) ?_
    exact FullBase.copyBaseMem_modulus hn32 hmod
  have htn0 : (MachineState.readWord (hitMem mem input n) 8224).toNat = 0 := by
    unfold hitMem Exp.storeWord
    rw [Challenge.EvmProof.Memory.readWord_writeWord]
    decide
  have hbound : 0 * Limbs.radix ^ n + Precompile.bytesToNatPadded input 96 (32 * n) < 2 * mm := by
    rw [Nat.zero_mul, Nat.zero_add]
    exact FullBase.baseValue_lt_two_mul (by omega) hodd hmod htop
  have h := Csub.csub_correct (hitMem mem input n) n _ mm 0 2048 hn hn32 hts hmodH htn0 (Nat.zero_le 1)
    hmpos hbound
  rw [Nat.zero_mul, Nat.zero_add] at h
  exact h

/-- Words at or above `ACC + 32 n` that `hitMem` and the first `CSUB` leave
alone, apart from `BASE` and `SUBB`. -/
theorem m1_readWord_disjoint (mem input : ByteArray) (n addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdisj : (addr + 32 ≤ 1024 ∨ 1024 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr)) :
    MachineState.readWord (m1Of mem input n) addr = MachineState.readWord mem addr := by
  unfold m1Of
  rw [Monpro.csResultMemory_readWord_outside _ n 2048 addr (by omega) hdisj.2.2.1 hdisj.2.1]
  unfold hitMem Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
    (by rw [Challenge.EvmProof.Memory.readPadded_size]; omega)]
  exact FullBase.copyBaseMem_readWord_disjoint mem input n addr hdisj.1

theorem m2_readWord_disjoint (mem input : ByteArray) (n addr : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32)
    (hdisj : (addr + 32 ≤ 1024 ∨ 1024 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2048 ∨ 2048 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ NEG ∨ NEG + 32 * n ≤ addr) ∧
      (addr + 32 ≤ PRE_L ∨ PRE_DINV + 32 ≤ addr) ∧
      (addr + 32 ≤ 7168 ∨ 7168 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 8224 ∨ 8256 + 32 * n ≤ addr)) :
    MachineState.readWord (m2Of mem input n) addr = MachineState.readWord mem addr := by
  unfold m2Of preMem
  rw [preMemOf_readWord_disjoint _ _ addr hdisj.2.2.2.1,
    negStep_readWord_disjoint _ n addr hdisj.2.2.1 n le_rfl]
  exact m1_readWord_disjoint mem input n addr hn hn32 ⟨hdisj.1, hdisj.2.1, hdisj.2.2.2.2⟩

/-- The step invariant at the shift loop entry. -/
theorem m2_stepInv (mem input : ByteArray) (n bsize mm minv : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hmpos : 0 < mm)
    (hframe : Exp.Frame mem n bsize minv) (hmod : Model.FastRepresents mem 0 n mm) :
    StepInv (m2Of mem input n) n bsize mm minv := by
  have hm2high : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (m2Of mem input n) addr = MachineState.readWord mem addr :=
    fun addr haddr => m2_readWord_disjoint mem input n addr (by omega) hn32
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by unfold NEG; omega),
        Or.inr (by unfold PRE_DINV; omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hframe2 : Exp.Frame (m2Of mem input n) n bsize minv :=
    ⟨by rw [hm2high 9344 le_rfl]; exact hframe.s32,
     by rw [hm2high 9376 (by omega)]; exact hframe.minvW,
     by rw [hm2high 9408 (by omega)]; exact hframe.ml,
     by rw [hm2high 9440 (by omega)]; exact hframe.tl,
     by rw [hm2high 9472 (by omega)]; exact hframe.eoff⟩
  have hmod1 : Model.FastRepresents (m1Of mem input n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact m1_readWord_disjoint mem input n _ (by omega) hn32
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩
  have hmod2 : Model.FastRepresents (m2Of mem input n) 0 n mm := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ 0 n mm (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 0 n mm (Or.inl (by unfold NEG; omega)) hmod1 n le_rfl)
  have hneg2 : Model.FastRepresents (m2Of mem input n) NEG n (Limbs.radix ^ n - mm) := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ NEG n _ (Or.inl (by unfold NEG PRE_L; omega))
      (neg_represents (m1Of mem input n) n mm (by omega) hn32 hmpos hmod1)
  exact ⟨hframe2, hmod2, hneg2⟩

/-- From the dispatcher entry on a hit to `BDONE`. -/
def gasSteps_hitPath (s : State) (mem input : ByteArray) (n bsize esize msize mm minv : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (e : Env s)
    (hdata : s.executionEnv.calldata = input) (hb : bsize < 2 ^ 256)
    (hmatch : FullBase.Matches mem n bsize)
    (hmpos : 0 < mm) (hodd : mm % 2 = 1) (hmm : mm < Limbs.radix ^ n)
    (hframe : Exp.Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm) :
    Challenge.EvmProof.GasSteps (dispState s mem n bsize esize msize)
      { Exp.bDone s (hitFinalMem mem input n mm) n bsize esize msize with pc := UInt256.ofNat 3324 } := by
  have htop : Limbs.radix ^ n < 2 * mm := R1.radix_pow_lt_two_mul (by omega) hodd hmod hmatch.2
  have hguard : Challenge.EvmProof.GasSteps (dispState s mem n bsize esize msize)
      (hitState s mem n bsize esize msize) := by
    have h := soundEnv blk2862 e
      (run_dispatch s mem n bsize esize msize hn32 hb e.act296 e.code e.run)
    rw [if_pos hmatch] at h
    exact h
  have hcsub0 := gasSteps_hitCsub s mem input n bsize esize msize hn hn32 e hdata hframe.ml
    hframe.tl hframe.s32
  -- facts at the shift loop entry
  have hm1high : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (m1Of mem input n) addr = MachineState.readWord mem addr :=
    fun addr haddr => m1_readWord_disjoint mem input n addr (by omega) hn32
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hm2high : ∀ addr, 9344 ≤ addr →
      MachineState.readWord (m2Of mem input n) addr = MachineState.readWord mem addr :=
    fun addr haddr => m2_readWord_disjoint mem input n addr (by omega) hn32
      ⟨Or.inr (by omega), Or.inr (by omega), Or.inr (by unfold NEG; omega),
        Or.inr (by unfold PRE_DINV; omega), Or.inr (by omega), Or.inr (by omega)⟩
  have hframe2 : Exp.Frame (m2Of mem input n) n bsize minv :=
    ⟨by rw [hm2high 9344 le_rfl]; exact hframe.s32,
     by rw [hm2high 9376 (by omega)]; exact hframe.minvW,
     by rw [hm2high 9408 (by omega)]; exact hframe.ml,
     by rw [hm2high 9440 (by omega)]; exact hframe.tl,
     by rw [hm2high 9472 (by omega)]; exact hframe.eoff⟩
  have hmod1 : Model.FastRepresents (m1Of mem input n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact m1_readWord_disjoint mem input n _ (by omega) hn32
      ⟨Or.inl (by omega), Or.inl (by omega), Or.inl (by omega), Or.inl (by omega)⟩
  have hmod2 : Model.FastRepresents (m2Of mem input n) 0 n mm := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ 0 n mm (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 0 n mm (Or.inl (by unfold NEG; omega)) hmod1 n le_rfl)
  have hneg2 : Model.FastRepresents (m2Of mem input n) NEG n (Limbs.radix ^ n - mm) := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ NEG n _ (Or.inl (by unfold NEG PRE_L; omega))
      (neg_represents (m1Of mem input n) n mm (by omega) hn32 hmpos hmod1)
  have hbase2 : Model.FastRepresents (m2Of mem input n) 2048 n
      (Precompile.bytesToNatPadded input 96 (32 * n) % mm) := by
    unfold m2Of preMem
    exact fastRepresents_preMemOf _ _ 2048 n _ (Or.inl (by unfold PRE_L; omega))
      (fastRepresents_negStep _ n 2048 n _ (Or.inl (by unfold NEG; omega))
        (m1_base mem input n mm hn hn32 hmpos hodd hmod hmatch.2) n le_rfl)
  have inv2 : StepInv (m2Of mem input n) n bsize mm minv := ⟨hframe2, hmod2, hneg2⟩
  have hpro := gasSteps_prologue s (m1Of mem input n) n bsize esize msize (by omega) hn32 e
    (by rw [hm1high 9408 (by omega)]; exact hframe.ml)
  have hloop := gasSteps_shiftLoop s (m2Of mem input n) n bsize esize msize mm minv _ hn hn32 e
    hmpos hmm htop inv2 hbase2 (Nat.mod_lt _ hmpos)
  have hexit : Challenge.EvmProof.GasSteps
      (shiftLoopState s (hitFinalMem mem input n mm) n bsize esize msize 0)
      { Exp.bDone s (hitFinalMem mem input n mm) n bsize esize msize with pc := UInt256.ofNat 3324 } :=
    (soundEnv blk3013 e
      (run_shiftHead_done s _ n bsize esize msize e.code e.run)).trans
    (soundEnv blk3264 e
      (run_shiftDone s _ n bsize esize msize e.code e.run))
  exact (((hguard.trans hcsub0).trans hpro).trans hloop).trans hexit

/-- From the dispatcher entry on a miss to the old `r0` block. -/
def gasSteps_missPath (s : State) (mem : ByteArray) (n bsize esize msize : Nat)
    (hn32 : n ≤ 32) (e : Env s) (hb : bsize < 2 ^ 256)
    (hmiss : ¬ FullBase.Matches mem n bsize) :
    Challenge.EvmProof.GasSteps (dispState s mem n bsize esize msize)
      (Exp.r0State s mem n bsize esize msize) := by
  have h := soundEnv blk2862 e
    (run_dispatch s mem n bsize esize msize hn32 hb e.act296 e.code e.run)
  rw [if_neg hmiss] at h
  exact h.trans (soundEnv blk2889 e (run_miss s mem n bsize esize msize e.code e.run))

end Challenge.Modexp.Submission.Proofs.Fast.Shift
