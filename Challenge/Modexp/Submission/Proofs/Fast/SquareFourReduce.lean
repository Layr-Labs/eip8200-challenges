import Challenge.Modexp.Submission.Proofs.Fast.SquareFourProducts

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.SquareFourReduce
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro SquareInit

def tail (mem : ByteArray) (c f : UInt256) : ByteArray :=
  storeWord (storeWord mem 2112 (MachineState.readWord mem 2080+c)) 2080
    (f + UInt256.lt (MachineState.readWord mem 2080+c) c)

def reduction (mem : ByteArray) (f : UInt256) : ByteArray :=
  let p := l2Step mem (rowMu mem 4) (rowC0 mem 4) 4 3
  tail p.memory p.carry f

theorem read_l2_outside (mem : ByteArray) (mu c : UInt256) (addr : Nat)
    (hd : addr+32 ≤ 2112 ∨ 2240 ≤ addr) :
    ∀ k, k ≤ 3 → MachineState.readWord (l2Step mem mu c 4 k).memory addr =
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
    (hd : addr+32 ≤ 2080 ∨ 2144 ≤ addr) :
    MachineState.readWord (tail mem c f) addr = MachineState.readWord mem addr := by
  rw [tail, read_storeWord_outside _ _ _ _ (by omega),
    read_storeWord_outside _ _ _ _ (by omega)]

theorem read_tail_top (mem : ByteArray) (c f : UInt256) :
    MachineState.readWord (tail mem c f) 2112 = MachineState.readWord mem 2080+c := by
  rw [tail, read_storeWord_outside _ _ _ _ (Or.inr (by decide)), read_storeWord]

theorem read_tail_high (mem : ByteArray) (c f : UInt256) :
    MachineState.readWord (tail mem c f) 2080 =
      f+UInt256.lt (MachineState.readWord mem 2080+c) c := by
  exact read_storeWord _ _ _

theorem read_reduction_outside (mem : ByteArray) (f : UInt256) (addr : Nat)
    (hd : addr+32 ≤ 2080 ∨ 2240 ≤ addr) :
    MachineState.readWord (reduction mem f) addr = MachineState.readWord mem addr := by
  rw [reduction, read_tail_outside _ _ _ _ (by omega),
    read_l2_outside _ _ _ _ (by omega) 3 (by decide)]

theorem reduction_low (mem : ByteArray) (f : UInt256) :
    Csub.lowValue (reduction mem f) 2112 4 4 =
      limbSum (fun k => (l2Val mem (rowMu mem 4) (rowC0 mem 4) 4 k).toNat) 3 +
        (MachineState.readWord mem 2080 +
          (l2Step mem (rowMu mem 4) (rowC0 mem 4) 4 3).carry).toNat*Limbs.radix^3 := by
  rw [← limbSum_eq_lowValue, limbSum_succ]
  have hlo : limbSum (fun k => (MachineState.readWord (reduction mem f)
          (2112+32*(4-1-k))).toNat) 3 =
      limbSum (fun k => (l2Val mem (rowMu mem 4) (rowC0 mem 4) 4 k).toNat) 3 := by
    apply limbSum_congr
    intro k hk
    rw [reduction, read_tail_outside _ _ _ _ (Or.inr (by omega))]
    simpa only [tAddr] using congrArg UInt256.toNat
      (readWord_l2Step_val mem (rowMu mem 4) (rowC0 mem 4) 4 k
        (by decide) (by omega) 3 hk (by decide))
  rw [hlo]
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  rw [reduction, read_tail_top,
    readWord_l2Step_low _ _ _ 4 2080 3 (by decide)]

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
    (hf : f.toNat ≤ 2) (hm : Model.FastRepresents mem 0 4 m)
    (hinv : ((MachineState.readWord mem 96).toNat *
      (MachineState.readWord mem 2816).toNat+1) % 2^256 = 0) :
    tValue (reduction mem f) 4 * Limbs.radix =
      (f.toNat*Limbs.radix+(MachineState.readWord mem 2080).toNat)*Limbs.radix^4 +
        Csub.lowValue mem 2112 4 4 + (rowMu mem 4).toNat*m := by
  let p := l2Step mem (rowMu mem 4) (rowC0 mem 4) 4 3
  let u := MachineState.readWord mem 2080
  let c := p.carry
  let cv := UInt256.lt (u+c) c
  have hcv : cv.toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have htn : (MachineState.readWord (reduction mem f) 2080).toNat = f.toNat+cv.toNat := by
    rw [reduction, read_tail_high, readWord_l2Step_low _ _ _ 4 2080 3 (by decide)]
    change (f+cv).toNat = f.toNat+cv.toNat
    rw [Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hB : cv.toNat*Limbs.radix+(u+c).toNat = u.toNat+c.toNat :=
    add_carry_split u c
  have hC : (rowC0 mem 4).toNat*Limbs.radix =
      (MachineState.readWord mem 2208).toNat +
        (MachineState.readWord mem 96).toNat*(rowMu mem 4).toNat :=
    c0_spec (MachineState.readWord mem 96) (MachineState.readWord mem 2816)
      (MachineState.readWord mem 2208) hinv
  have hD := l2_invariant mem (rowMu mem 4) (rowC0 mem 4) 4 (by decide) 3 (by decide)
  have hE : limbSum (fun k =>
          (MachineState.readWord mem (2112+32*(4-2-k))).toNat) 3*Limbs.radix +
        (MachineState.readWord mem 2208).toNat = Csub.lowValue mem 2112 4 4 := by
    have he := limbSum_shift (fun k =>
      (MachineState.readWord mem (2112+32*(4-1-k))).toNat) 3
    have haddr : (fun k => (MachineState.readWord mem (2112+32*(4-1-(k+1)))).toNat) =
        (fun k => (MachineState.readWord mem (2112+32*(4-2-k))).toNat) := by
      funext k
      congr 2
      omega
    rw [haddr, limbSum_eq_lowValue] at he
    exact he
  have hF : limbSum (fun k =>
          (MachineState.readWord mem (32*(4-2-k))).toNat) 3*Limbs.radix +
        (MachineState.readWord mem 96).toNat = m := by
    have he := limbSum_shift (fun k =>
      (MachineState.readWord mem (0+32*(4-1-k))).toNat) 3
    have haddr : (fun k => (MachineState.readWord mem (0+32*(4-1-(k+1)))).toNat) =
        (fun k => (MachineState.readWord mem (32*(4-2-k))).toNat) := by
      funext k
      congr 2
      omega
    rw [haddr, limbSum_fastRepresents hm] at he
    exact he
  rw [tValue, htn, reduction_low]
  have hp : Limbs.radix^4 = Limbs.radix^3*Limbs.radix := pow_succ _ 3
  rw [hp]
  exact reduction_alg hB hC hD hE hF

end Challenge.Modexp.Submission.Proofs.Fast.SquareFourReduce
