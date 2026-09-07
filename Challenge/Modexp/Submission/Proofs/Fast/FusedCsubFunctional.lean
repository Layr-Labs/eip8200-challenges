import Challenge.Modexp.Submission.Proofs.Fast.FusedCsub
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Functional contract of the fused ADDMOD/CSUB walk

The proof is independent of benchmark inputs.  It assumes only the public fast
path geometry: the operand blocks end before `SUBB`, the modulus has at most 32
limbs, and the modular-add inputs satisfy the existing `< 2m` contract.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FusedCsub

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

/-! ## One-limb arithmetic -/

/-- The instruction ordering used by the fused loop: first add the two data
limbs, then add the incoming carry, and detect overflow against the first sum. -/
theorem addLimb_spec (x y c : UInt256) (hc : c.toNat ≤ 1) :
    ((x + y) + c).toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt ((x + y) + c) (x + y))
          (UInt256.lt (x + y) x)).toNat =
      x.toNat + y.toNat + c.toNat ∧
    (UInt256.lor (UInt256.lt ((x + y) + c) (x + y))
      (UInt256.lt (x + y) x)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt ((x + y) + c) (x + y)).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have h2 : (UInt256.lt (x + y) x).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, Csub.or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_add, Limbs.radix]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

/-- For a one-bit incoming borrow, the bytecode's wrap-detection form
`d < d - b` is exactly the usual `d < b` predicate. -/
theorem lt_sub_borrow_eq (d b : UInt256) (_hb : b.toNat ≤ 1) :
    UInt256.lt d (d - b) = UInt256.lt d b :=
  lt_sub_eq_lt d b

theorem lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_lor, Nat.or_comm]

/-! ## Concrete limb projections -/

theorem limbStep_lowValue_ts_stable (memory : ByteArray) (pa pb n j : Nat)
    (hj : j < n) :
    Csub.lowValue (limbStep memory pa pb n (j + 1)).memory 8256 n j =
      Csub.lowValue (limbStep memory pa pb n j).memory 8256 n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [limbStep]
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]

theorem limbStep_lowValue_sub_stable (memory : ByteArray) (pa pb n j : Nat)
    (hj : j < n) (hn32 : n ≤ 32) :
    Csub.lowValue (limbStep memory pa pb n (j + 1)).memory 7168 n j =
      Csub.lowValue (limbStep memory pa pb n j).memory 7168 n j := by
  apply Csub.lowValue_congr
  intro k hk
  simp only [limbStep]
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]

theorem limbStep_readWord_new_ts (memory : ByteArray) (pa pb n j : Nat) :
    MachineState.readWord (limbStep memory pa pb n (j + 1)).memory
        (8256 + 32 * (n - 1 - j)) =
      (MachineState.readWord (limbStep memory pa pb n j).memory
          (pa + 32 * (n - 1 - j)) +
        MachineState.readWord (limbStep memory pa pb n j).memory
          (pb + 32 * (n - 1 - j))) +
        (limbStep memory pa pb n j).carry := by
  simp only [limbStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem limbStep_readWord_new_sub (memory : ByteArray) (pa pb n j : Nat) :
    MachineState.readWord (limbStep memory pa pb n (j + 1)).memory
        (7168 + 32 * (n - 1 - j)) =
      ((MachineState.readWord (limbStep memory pa pb n j).memory
          (pa + 32 * (n - 1 - j)) +
        MachineState.readWord (limbStep memory pa pb n j).memory
          (pb + 32 * (n - 1 - j))) +
        (limbStep memory pa pb n j).carry) -
        MachineState.readWord (limbStep memory pa pb n j).memory
          (32 * (n - 1 - j)) -
        (limbStep memory pa pb n j).borrow := by
  simp only [limbStep]
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

@[simp] theorem limbStep_carry_succ (memory : ByteArray) (pa pb n j : Nat) :
    (limbStep memory pa pb n (j + 1)).carry =
      UInt256.lor
        (UInt256.lt
          ((MachineState.readWord (limbStep memory pa pb n j).memory
              (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (limbStep memory pa pb n j).memory
              (pb + 32 * (n - 1 - j))) +
            (limbStep memory pa pb n j).carry)
          (MachineState.readWord (limbStep memory pa pb n j).memory
              (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (limbStep memory pa pb n j).memory
              (pb + 32 * (n - 1 - j))))
        (UInt256.lt
          (MachineState.readWord (limbStep memory pa pb n j).memory
              (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (limbStep memory pa pb n j).memory
              (pb + 32 * (n - 1 - j)))
          (MachineState.readWord (limbStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)))) := by
  simp only [limbStep]

@[simp] theorem limbStep_borrow_succ (memory : ByteArray) (pa pb n j : Nat) :
    (limbStep memory pa pb n (j + 1)).borrow =
      let total :=
        (MachineState.readWord (limbStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)) +
          MachineState.readWord (limbStep memory pa pb n j).memory
            (pb + 32 * (n - 1 - j))) +
          (limbStep memory pa pb n j).carry
      let md := MachineState.readWord (limbStep memory pa pb n j).memory
        (32 * (n - 1 - j))
      let d1 := total - md
      let d2 := d1 - (limbStep memory pa pb n j).borrow
      UInt256.lor (UInt256.lt d1 d2) (UInt256.lt total d1) := by
  simp only [limbStep]

/-- Semantic form consumed by the existing conditional-subtraction algebra. -/
theorem limbStep_borrow_succ_spec (memory : ByteArray) (pa pb n j : Nat)
    (hb : (limbStep memory pa pb n j).borrow.toNat ≤ 1) :
    (limbStep memory pa pb n (j + 1)).borrow =
      let total :=
        (MachineState.readWord (limbStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)) +
          MachineState.readWord (limbStep memory pa pb n j).memory
            (pb + 32 * (n - 1 - j))) +
          (limbStep memory pa pb n j).carry
      let md := MachineState.readWord (limbStep memory pa pb n j).memory
        (32 * (n - 1 - j))
      UInt256.lor (UInt256.lt total md)
        (UInt256.lt (total - md) (limbStep memory pa pb n j).borrow) := by
  simp only [limbStep]
  rw [lt_sub_borrow_eq _ _ hb, lt_sub_eq_lt, lor_comm]

/-! ## The two simultaneous invariants -/

/-- The `TS` projection is the usual carry-propagating addition.  The stronger
operand bound is the live fast-path layout and prevents the interleaved `SUBB`
stores from becoming source writes. -/
theorem add_invariant (memory : ByteArray) (pa pb n : Nat)
    (_hn : 1 ≤ n) (hpa : pa + 32 * n ≤ 7168) (hpb : pb + 32 * n ≤ 7168) :
    ∀ j, j ≤ n →
      Csub.lowValue (limbStep memory pa pb n j).memory 8256 n j +
            (limbStep memory pa pb n j).carry.toNat * Limbs.radix ^ j =
          Csub.lowValue memory pa n j + Csub.lowValue memory pb n j ∧
        (limbStep memory pa pb n j).carry.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [limbStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxa : MachineState.readWord (limbStep memory pa pb n j).memory
          (pa + 32 * (n - 1 - j)) =
          MachineState.readWord memory (pa + 32 * (n - 1 - j)) :=
        limbStep_readWord_disjoint memory pa pb n _ (Or.inl (by omega))
          (Or.inl (by omega)) j (by omega)
      have hxb : MachineState.readWord (limbStep memory pa pb n j).memory
          (pb + 32 * (n - 1 - j)) =
          MachineState.readWord memory (pb + 32 * (n - 1 - j)) :=
        limbStep_readWord_disjoint memory pa pb n _ (Or.inl (by omega))
          (Or.inl (by omega)) j (by omega)
      have hlimb := addLimb_spec
        (MachineState.readWord memory (pa + 32 * (n - 1 - j)))
        (MachineState.readWord memory (pb + 32 * (n - 1 - j)))
        (limbStep memory pa pb n j).carry ihLe
      rw [Csub.lowValue_succ (limbStep memory pa pb n (j + 1)).memory 8256 n j,
        limbStep_lowValue_ts_stable memory pa pb n j (by omega),
        limbStep_readWord_new_ts, limbStep_carry_succ,
        Csub.lowValue_succ memory pa n j, Csub.lowValue_succ memory pb n j, pow_succ]
      simp only [hxa, hxb]
      exact ⟨Csub.am_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

/-- The `SUBB` projection is the usual borrow-propagating subtraction, using
the just-produced `TS` limb in each fused iteration. -/
theorem sub_invariant (memory : ByteArray) (pa pb n : Nat)
    (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    ∀ j, j ≤ n →
      Csub.lowValue (limbStep memory pa pb n j).memory 7168 n j +
          Csub.lowValue memory 0 n j =
        Csub.lowValue (limbStep memory pa pb n j).memory 8256 n j +
          (limbStep memory pa pb n j).borrow.toNat * Limbs.radix ^ j ∧
        (limbStep memory pa pb n j).borrow.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [limbStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxm : MachineState.readWord (limbStep memory pa pb n j).memory
          (32 * (n - 1 - j)) = MachineState.readWord memory (32 * (n - 1 - j)) :=
        limbStep_readWord_disjoint memory pa pb n _ (Or.inl (by omega))
          (Or.inl (by omega)) j (by omega)
      let total :=
        (MachineState.readWord (limbStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)) +
          MachineState.readWord (limbStep memory pa pb n j).memory
            (pb + 32 * (n - 1 - j))) +
          (limbStep memory pa pb n j).carry
      have hlimb := Csub.subLimb_spec total
        (MachineState.readWord memory (32 * (n - 1 - j)))
        (limbStep memory pa pb n j).borrow ihLe
      rw [Csub.lowValue_succ (limbStep memory pa pb n (j + 1)).memory 7168 n j,
        limbStep_lowValue_sub_stable memory pa pb n j (by omega) hn32,
        limbStep_readWord_new_sub,
        Csub.lowValue_succ memory 0 n j,
        Csub.lowValue_succ (limbStep memory pa pb n (j + 1)).memory 8256 n j,
        limbStep_lowValue_ts_stable memory pa pb n j (by omega),
        limbStep_readWord_new_ts, limbStep_borrow_succ_spec _ _ _ _ _ ihLe, pow_succ]
      simp only [Nat.zero_add, hxm]
      exact ⟨Csub.cs_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

/-! ## Memory representation and selection -/

def resultMemory (memory : ByteArray) (pa pb n pd : Nat) : ByteArray :=
  MachineState.writeBytes (tnMemory memory pa pb n n)
    (MachineState.readPadded (tnMemory memory pa pb n n)
      (resultSrc memory pa pb n n).toNat (32 * n)) pd

/-- The fused result transformer leaves the configuration area untouched. -/
theorem resultMemory_readWord_high (memory : ByteArray) (pa pb n pd addr : Nat)
    (_hn : 1 ≤ n) (hn32 : n ≤ 32) (hpd : pd + 32 * n ≤ 8192)
    (haddr : 9344 ≤ addr) :
    MachineState.readWord (resultMemory memory pa pb n pd) addr =
      MachineState.readWord memory addr := by
  have hsize : (MachineState.readPadded (tnMemory memory pa pb n n)
      (resultSrc memory pa pb n n).toNat (32 * n)).size = 32 * n :=
    Challenge.EvmProof.Memory.readPadded_size _ _ _
  unfold resultMemory
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
      (Or.inr (by rw [hsize]; omega))]
  exact tnMemory_readWord_disjoint memory pa pb n n addr
    (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega)) (by omega)

theorem returnedState_memory (s : State) (memory : ByteArray) (pa pb n pd : Nat)
    (ret : UInt256) (rest : List UInt256) (hpd : pd < 2 ^ 256) :
    (returnedState s memory pa pb n n (UInt256.ofNat pd) ret rest).memory =
      resultMemory memory pa pb n pd := by
  simp only [returnedState, resultMemory]
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hpd]

theorem useSub_toNat (memory : ByteArray) (pa pb n j : Nat)
    (hcarry : (limbStep memory pa pb n j).carry.toNat ≤ 1) :
    (useSub memory pa pb n j).toNat =
      max (limbStep memory pa pb n j).carry.toNat
        (if (limbStep memory pa pb n j).borrow.toNat = 0 then 1 else 0) := by
  have hz : (UInt256.isZero (limbStep memory pa pb n j).borrow).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_isZero]
    split <;> omega
  rw [useSub, Challenge.EvmProof.Word.word_toNat_lor, Csub.or_of_le_one hcarry hz,
    Challenge.EvmProof.Word.word_toNat_isZero]

theorem fastRepresents_limbStep (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hsub : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hts : ptr + 32 * cnt ≤ 8256 ∨ 8256 + 32 * n ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) (j : Nat) (hj : j ≤ n) :
    Model.FastRepresents (limbStep memory pa pb n j).memory ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact limbStep_readWord_disjoint memory pa pb n _ (by omega) (by omega) j hj

theorem fastRepresents_tnMemory (memory : ByteArray) (pa pb n ptr cnt v : Nat)
    (hsub : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hts : ptr + 32 * cnt ≤ 8256 ∨ 8256 + 32 * n ≤ ptr)
    (htn : ptr + 32 * cnt ≤ 8224 ∨ 8256 ≤ ptr)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (tnMemory memory pa pb n n) ptr cnt v := by
  unfold tnMemory
  exact Model.fastRepresents_writeWord_disjoint _ 8224 ptr cnt v _
    (htn.elim Or.inr Or.inl)
    (fastRepresents_limbStep memory pa pb n ptr cnt v hsub hts hrep n le_rfl)

/-- The fused routine returns the same modular sum contract as the sequential
implementation. -/
theorem addmod_correct (memory : ByteArray) (pa pb n a b mm pd : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32)
    (hpa : pa + 32 * n ≤ 7168) (hpb : pb + 32 * n ≤ 7168)
    (ha : Model.FastRepresents memory pa n a)
    (hb : Model.FastRepresents memory pb n b)
    (hm : Model.FastRepresents memory 0 n mm) (_hmpos : 0 < mm)
    (hab : a + b < 2 * mm) :
    Model.FastRepresents (resultMemory memory pa pb n pd) pd n ((a + b) % mm) := by
  obtain ⟨hadd, hcarry⟩ := add_invariant memory pa pb n (by omega) hpa hpb n le_rfl
  obtain ⟨hsub, hborrow⟩ := sub_invariant memory pa pb n (by omega) hn32 n le_rfl
  have hA : Csub.lowValue memory pa n n = a := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents ha
  have hB : Csub.lowValue memory pb n n = b := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hb
  have hM : Csub.lowValue memory 0 n n = mm := by
    rw [Csub.lowValue_full]; exact Model.value_of_fastRepresents hm
  rw [hA, hB] at hadd
  rw [hM] at hsub
  let T := Csub.lowValue (limbStep memory pa pb n n).memory 8256 n n
  let D := Csub.lowValue (limbStep memory pa pb n n).memory 7168 n n
  let carry := (limbStep memory pa pb n n).carry.toNat
  let borrow := (limbStep memory pa pb n n).borrow.toNat
  have hT : T < Limbs.radix ^ n := Csub.lowValue_lt _ _ _ _
  have hD : D < Limbs.radix ^ n := Csub.lowValue_lt _ _ _ _
  have hmR : mm < Limbs.radix ^ n := hm.1
  have huseLe := useSub_le_one memory pa pb n n hcarry
  have huse : (useSub memory pa pb n n).toNat =
      max carry (if borrow = 0 then 1 else 0) := by
    simpa only [carry, borrow] using useSub_toNat memory pa pb n n hcarry
  have hsubb : Model.FastRepresents (tnMemory memory pa pb n n) 7168 n D := by
    unfold D
    exact Model.fastRepresents_writeWord_disjoint _ 8224 7168 n _ _ (by omega)
      (Csub.fastRepresents_lowValue _ _ _)
  have hts : Model.FastRepresents (tnMemory memory pa pb n n) 8256 n T := by
    unfold T
    exact Model.fastRepresents_writeWord_disjoint _ 8224 8256 n _ _ (by omega)
      (Csub.fastRepresents_lowValue _ _ _)
  by_cases huse0 : (useSub memory pa pb n n).toNat = 0
  · have huse0' : max carry (if borrow = 0 then 1 else 0) = 0 := by
      rw [← huse]; exact huse0
    have hc0 : carry = 0 := by omega
    have hb1 : borrow = 1 := by
      by_contra hc
      have hb0 : borrow = 0 := by omega
      rw [hb0, if_pos rfl] at huse0'
      omega
    dsimp only [carry] at hc0
    dsimp only [borrow] at hb1
    rw [hc0, Nat.zero_mul, Nat.add_zero] at hadd
    rw [hb1, Nat.one_mul] at hsub
    have hlt : a + b < mm := by
      dsimp only [T, D, carry, borrow] at hadd hsub hT hD ⊢
      omega
    have hmod : (a + b) % mm = a + b := Nat.mod_eq_of_lt hlt
    rw [hmod, ← hadd]
    unfold resultMemory
    rw [resultSrc_toNat memory pa pb n n huseLe, if_pos huse0]
    exact Csub.fastRepresents_mcopy _ _ _ _ _ (by omega) hts
  · have huse1' : max carry (if borrow = 0 then 1 else 0) = 1 := by
      rw [← huse]
      omega
    have hcases : carry = 1 ∨ borrow = 0 := by
      by_cases hb : borrow = 0
      · exact Or.inr hb
      · rw [if_neg hb] at huse1'
        left
        omega
    have hval : D + mm = a + b := by
      rcases hcases with hc1 | hb0
      · have hb1 : borrow = 1 := by
          by_contra hc
          have hb0 : borrow = 0 := by omega
          dsimp only [borrow] at hb0
          dsimp only [carry] at hc1
          rw [hb0, Nat.zero_mul, Nat.add_zero] at hsub
          rw [hc1, Nat.one_mul] at hadd
          dsimp only [T, D, carry, borrow] at hsub hadd hT hD hmR hab
          omega
        dsimp only [borrow] at hb1
        dsimp only [carry] at hc1
        rw [hb1, Nat.one_mul] at hsub
        rw [hc1, Nat.one_mul] at hadd
        dsimp only [T, D] at hsub hadd ⊢
        omega
      · dsimp only [borrow] at hb0
        rw [hb0, Nat.zero_mul, Nat.add_zero] at hsub
        have hc0 : carry = 0 := by
          by_contra hc
          have hc1 : carry = 1 := by omega
          dsimp only [carry] at hc1
          rw [hc1, Nat.one_mul] at hadd
          dsimp only [T, D, carry, borrow] at hsub hadd hT hD hmR hab
          omega
        dsimp only [carry] at hc0
        rw [hc0, Nat.zero_mul, Nat.add_zero] at hadd
        dsimp only [T, D] at hsub hadd ⊢
        omega
    have hmod : (a + b) % mm = D := by
      rw [Model.mod_eq_cond_sub_of_lt_twice hab, if_neg (by omega)]
      omega
    rw [hmod]
    unfold resultMemory
    rw [resultSrc_toNat memory pa pb n n huseLe, if_neg huse0]
    exact Csub.fastRepresents_mcopy _ _ _ _ _ (by omega) hsubb

/-- A represented block outside both scratch blocks and the destination is
preserved by the fused call. -/
theorem addmod_preserves_region (memory : ByteArray) (pa pb n pd ptr cnt v : Nat)
    (hsub : ptr + 32 * cnt ≤ 7168 ∨ 7168 + 32 * n ≤ ptr)
    (hts : ptr + 32 * cnt ≤ 8256 ∨ 8256 + 32 * n ≤ ptr)
    (htn : ptr + 32 * cnt ≤ 8224 ∨ 8256 ≤ ptr)
    (hdst : pd + 32 * n ≤ ptr ∨ ptr + 32 * cnt ≤ pd)
    (hrep : Model.FastRepresents memory ptr cnt v) :
    Model.FastRepresents (resultMemory memory pa pb n pd) ptr cnt v := by
  unfold resultMemory
  exact Csub.fastRepresents_mcopy_disjoint _ _ _ _ _ _ _ hdst
    (fastRepresents_tnMemory memory pa pb n ptr cnt v hsub hts htn hrep)

end Challenge.Modexp.Submission.Proofs.Fast.FusedCsub
