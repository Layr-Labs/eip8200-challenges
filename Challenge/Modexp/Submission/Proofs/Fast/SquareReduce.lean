import Challenge.Modexp.Submission.Proofs.Fast.SquareProducts

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareReduce
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareInit

def tail (mem : ByteArray) (c f : UInt256) : ByteArray :=
  storeWord (storeWord mem 8256 (MachineState.readWord mem 8224+c)) 8224
    (f + UInt256.lt (MachineState.readWord mem 8224+c) c)

def reduction (mem : ByteArray) (f : UInt256) : ByteArray :=
  let p := l2Step mem (rowMu mem 8) (rowC0 mem 8) 8 7
  tail p.memory p.carry f

theorem read_l2_outside (mem : ByteArray) (mu c : UInt256) (addr : Nat)
    (hd : addr+32 ≤ 8256 ∨ 8512 ≤ addr) :
    ∀ k, k ≤ 7 → MachineState.readWord (l2Step mem mu c 8 k).memory addr =
      MachineState.readWord mem addr := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro hk
    simp only [l2Step]
    change MachineState.readWord (storeWord _ _ _) addr = _
    rw [read_storeWord_outside _ _ _ _ (by omega)]
    exact ih (by omega)

theorem read_tail_outside (mem : ByteArray) (c f : UInt256) (addr : Nat)
    (hd : addr+32 ≤ 8224 ∨ 8288 ≤ addr) :
    MachineState.readWord (tail mem c f) addr = MachineState.readWord mem addr := by
  rw [tail, read_storeWord_outside _ _ _ _ (by omega),
    read_storeWord_outside _ _ _ _ (by omega)]

theorem read_tail_top (mem : ByteArray) (c f : UInt256) :
    MachineState.readWord (tail mem c f) 8256 = MachineState.readWord mem 8224+c := by
  rw [tail, read_storeWord_outside _ _ _ _ (Or.inr (by decide)), read_storeWord]

theorem read_tail_high (mem : ByteArray) (c f : UInt256) :
    MachineState.readWord (tail mem c f) 8224 =
      f+UInt256.lt (MachineState.readWord mem 8224+c) c := by
  exact read_storeWord _ _ _

theorem read_reduction_outside (mem : ByteArray) (f : UInt256) (addr : Nat)
    (hd : addr+32 ≤ 8224 ∨ 8512 ≤ addr) :
    MachineState.readWord (reduction mem f) addr = MachineState.readWord mem addr := by
  rw [reduction, read_tail_outside _ _ _ _ (by omega),
    read_l2_outside _ _ _ _ (by omega) 7 (by decide)]

theorem reduction_low (mem : ByteArray) (f : UInt256) :
    Csub.lowValue (reduction mem f) 8256 8 8 =
      limbSum (fun k => (l2Val mem (rowMu mem 8) (rowC0 mem 8) 8 k).toNat) 7 +
        (MachineState.readWord mem 8224 +
          (l2Step mem (rowMu mem 8) (rowC0 mem 8) 8 7).carry).toNat*Limbs.radix^7 := by
  rw [← limbSum_eq_lowValue, limbSum_succ]
  have hlo : limbSum (fun k => (MachineState.readWord (reduction mem f)
          (8256+32*(8-1-k))).toNat) 7 =
      limbSum (fun k => (l2Val mem (rowMu mem 8) (rowC0 mem 8) 8 k).toNat) 7 := by
    apply limbSum_congr
    intro k hk
    rw [reduction, read_tail_outside _ _ _ _ (Or.inr (by omega))]
    simpa only [tAddr] using congrArg UInt256.toNat
      (readWord_l2Step_val mem (rowMu mem 8) (rowC0 mem 8) 8 k
        (by decide) (by omega) 7 hk (by decide))
  rw [hlo]
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  rw [reduction, read_tail_top,
    readWord_l2Step_low _ _ _ 8 8224 7 (by decide)]

private theorem reduction_alg {f cv R P v u C c0 T0 M0 S St Sm q m L : Nat}
    (hB : cv*R+v = u+C)
    (hC : c0*R = T0+M0*q)
    (hD : S+C*P = c0+(St+q*Sm))
    (hE : St*R+T0 = L) (hF : Sm*R+M0 = m) :
    ((f+cv)*(P*R)+(S+v*P))*R = (f*R+u)*(P*R)+L+q*m := by
  calc
    _ = f*R*(P*R)+(cv*R+v)*(P*R)+S*R := by ring
    _ = f*R*(P*R)+(u+C)*(P*R)+S*R := by rw [hB]
    _ = (f*R+u)*(P*R)+(S+C*P)*R := by ring
    _ = (f*R+u)*(P*R)+(c0+(St+q*Sm))*R := by rw [hD]
    _ = (f*R+u)*(P*R)+(c0*R+St*R+q*(Sm*R)) := by ring
    _ = (f*R+u)*(P*R)+(T0+M0*q+St*R+q*(Sm*R)) := by rw [hC]
    _ = (f*R+u)*(P*R)+(St*R+T0)+q*(Sm*R+M0) := by ring
    _ = _ := by rw [hE, hF]

/-- The common reduction chain is exact even with two incoming overflow bits. -/
theorem reduction_equation (mem : ByteArray) (f : UInt256) (m : Nat)
    (hf : f.toNat ≤ 2) (hm : Model.FastRepresents mem 0 8 m)
    (hinv : ((MachineState.readWord mem 224).toNat *
      (MachineState.readWord mem 9376).toNat+1) % 2^256 = 0) :
    tValue (reduction mem f) 8 * Limbs.radix =
      (f.toNat*Limbs.radix+(MachineState.readWord mem 8224).toNat)*Limbs.radix^8 +
        Csub.lowValue mem 8256 8 8 + (rowMu mem 8).toNat*m := by
  let p := l2Step mem (rowMu mem 8) (rowC0 mem 8) 8 7
  let u := MachineState.readWord mem 8224
  let c := p.carry
  let cv := UInt256.lt (u+c) c
  have hcv : cv.toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have htn : (MachineState.readWord (reduction mem f) 8224).toNat = f.toNat+cv.toNat := by
    rw [reduction, read_tail_high, readWord_l2Step_low _ _ _ 8 8224 7 (by decide)]
    change (f+cv).toNat = f.toNat+cv.toNat
    rw [Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hB : cv.toNat*Limbs.radix+(u+c).toNat = u.toNat+c.toNat :=
    add_carry_split u c
  have hC : (rowC0 mem 8).toNat*Limbs.radix =
      (MachineState.readWord mem 8480).toNat +
        (MachineState.readWord mem 224).toNat*(rowMu mem 8).toNat :=
    c0_spec (MachineState.readWord mem 224) (MachineState.readWord mem 9376)
      (MachineState.readWord mem 8480) hinv
  have hD := l2_invariant mem (rowMu mem 8) (rowC0 mem 8) 8 (by decide) 7 (by decide)
  have hE : limbSum (fun k =>
          (MachineState.readWord mem (8256+32*(8-2-k))).toNat) 7*Limbs.radix +
        (MachineState.readWord mem 8480).toNat = Csub.lowValue mem 8256 8 8 := by
    have he := limbSum_shift (fun k =>
      (MachineState.readWord mem (8256+32*(8-1-k))).toNat) 7
    have haddr : (fun k => (MachineState.readWord mem (8256+32*(8-1-(k+1)))).toNat) =
        (fun k => (MachineState.readWord mem (8256+32*(8-2-k))).toNat) := by
      funext k
      congr 2
      omega
    rw [haddr, limbSum_eq_lowValue] at he
    exact he
  have hF : limbSum (fun k =>
          (MachineState.readWord mem (32*(8-2-k))).toNat) 7*Limbs.radix +
        (MachineState.readWord mem 224).toNat = m := by
    have he := limbSum_shift (fun k =>
      (MachineState.readWord mem (0+32*(8-1-k))).toNat) 7
    have haddr : (fun k => (MachineState.readWord mem (0+32*(8-1-(k+1)))).toNat) =
        (fun k => (MachineState.readWord mem (32*(8-2-k))).toNat) := by
      funext k
      congr 2
      omega
    rw [haddr, limbSum_fastRepresents hm] at he
    exact he
  rw [tValue, htn, reduction_low]
  have hp : Limbs.radix^8 = Limbs.radix^7*Limbs.radix := pow_succ _ 7
  rw [hp]
  exact reduction_alg hB hC hD hE hF

end Challenge.Modexp.Submission.Proofs.Fast.SquareReduce
