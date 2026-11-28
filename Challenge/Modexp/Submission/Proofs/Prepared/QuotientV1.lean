import Challenge.Modexp.Submission.Proofs.Prepared.TopResidualBound
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
/-! Quotient estimate of the conversion step with the correction constant pre-shifted.

The heads compare `(q >> 128) * c'` with `rho = (X >> K) mod D'`, where `c' = (N1 >> 128) >> K` is
computed once per conversion and kept in the frame. Since `c' * 2^K ≤ N1 >> 128` and
`X - D*q = 2^K * rho + (X mod 2^K) < 2^K * (rho + 1)`, a decrement taken by this test is also taken
by the full test of `qhatOf`, so the estimate is never below `qhatOf` and never above `X / D`. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.Shift
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs Challenge.Modexp.Submission.Proofs.Fast
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.QHat
/-- The correction constant: `(N1 >> 128) >> K`. -/
def corrOf (mem : ByteArray) : UInt256 :=
  UInt256.shiftRight (UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128))
    (MachineState.readWord mem PRE_L)
def eDecV1 (mem : ByteArray) : UInt256 :=
  UInt256.gt (UInt256.shiftRight (eQ mem) (UInt256.ofNat 128) * corrOf mem) (eRho mem)
def qhatV1 (mem : ByteArray) : UInt256 :=
  UInt256.lor (UInt256.ofNat 0 -
      UInt256.isZero (UInt256.lt (eHi mem) (MachineState.readWord mem PRE_DODD)))
    (eQ mem - eDecV1 mem)
/-- The saturating select shared by `qhatOf` and `qhatV1`. -/
theorem sat_select_toNat (h e d D : UInt256) (hde : d.toNat ≤ e.toNat) :
    (UInt256.lor (UInt256.ofNat 0 - UInt256.isZero (UInt256.lt h D)) (e - d)).toNat =
      if h.toNat < D.toNat then e.toNat - d.toNat else 2 ^ 256 - 1 := by
  by_cases hs : h.toNat < D.toNat
  · rw [if_pos hs]
    have hlt : UInt256.lt h D = UInt256.ofNat 1 := by
      unfold UInt256.lt; rw [if_pos hs]
    have hz : UInt256.isZero (UInt256.ofNat 1) = UInt256.ofNat 0 := by
      unfold UInt256.isZero; rw [if_neg (by simp)]
    have hsub : UInt256.ofNat 0 - UInt256.ofNat 0 = UInt256.ofNat 0 := by
      apply Challenge.EvmProof.Word.word_ext
      simp [word_toNat_sub,word_toNat_ofNat]
    rw [hlt,hz,hsub,word_toNat_lor,word_toNat_ofNat]
    simp only [Nat.zero_mod,Nat.zero_or]
    rw [word_toNat_sub]
    have h1 : e.toNat < 2 ^ 256 := e.val.isLt
    have h2 : d.toNat < 2 ^ 256 := d.val.isLt
    omega
  · rw [if_neg hs]
    have hlt : UInt256.lt h D = UInt256.ofNat 0 := by
      unfold UInt256.lt; rw [if_neg hs]
    have hz : UInt256.isZero (UInt256.ofNat 0) = UInt256.ofNat 1 := by
      unfold UInt256.isZero; rw [if_pos (by simp)]
    have hsub : (UInt256.ofNat 0 - UInt256.ofNat 1).toNat = 2 ^ 256 - 1 := by
      rw [word_toNat_sub,word_toNat_ofNat,word_toNat_ofNat]
      norm_num
    rw [hlt,hz,word_toNat_lor,hsub]
    exact QHat.or_two_pow_sub_one 256 _ (e - d).val.isLt
/-- `u0 - D * q` is computed exactly when `q = X / D`: it is `X mod D`. -/
theorem rhat_toNat (u1 u0 D q : UInt256) (hD : 0 < D.toNat)
    (hq : q.toNat = (u1.toNat * 2 ^ 256 + u0.toNat) / D.toNat) :
    (u0 - D * q).toNat = (u1.toNat * 2 ^ 256 + u0.toNat) % D.toNat := by
  rw [word_toNat_sub,Setup.word_toNat_mul,hq]
  set X := u1.toNat * 2 ^ 256 + u0.toNat with hX
  set P := D.toNat * (X / D.toNat) with hP
  have hR : X % D.toNat < 2 ^ 256 := lt_trans (Nat.mod_lt _ hD) D.val.isLt
  have hu0 : u0.toNat < 2 ^ 256 := u0.val.isLt
  have hPR : P + X % D.toNat = X := Nat.div_add_mod X D.toNat
  have hPm : P % 2 ^ 256 < 2 ^ 256 := Nat.mod_lt _ (by positivity)
  -- (P mod B + R) ≡ u0 (mod B)
  have hcong : (P % 2 ^ 256 + X % D.toNat) % 2 ^ 256 = u0.toNat := by
    have : (P + X % D.toNat) % 2 ^ 256 = u0.toNat := by
      rw [hPR,hX,Nat.add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hu0]
    rw [← this,Nat.add_mod,Nat.mod_mod,← Nat.add_mod]
  have hcases : P % 2 ^ 256 + X % D.toNat = u0.toNat ∨
      P % 2 ^ 256 + X % D.toNat = u0.toNat + 2 ^ 256 := by
    have hlt2 : P % 2 ^ 256 + X % D.toNat < 2 * 2 ^ 256 := by omega
    rcases Nat.lt_or_ge (P % 2 ^ 256 + X % D.toNat) (2 ^ 256) with h | h
    · left; rw [Nat.mod_eq_of_lt h] at hcong; exact hcong
    · right
      have h2 : (P % 2 ^ 256 + X % D.toNat) % 2 ^ 256 = P % 2 ^ 256 + X % D.toNat - 2 ^ 256 := by
        rw [Nat.mod_eq_sub_mod h,Nat.mod_eq_of_lt (by omega)]
      omega
  rcases hcases with h | h
  · rw [show 2 ^ 256 + u0.toNat - P % 2 ^ 256 = X % D.toNat + 2 ^ 256 by omega,
      Nat.add_mod_right,Nat.mod_eq_of_lt hR]
  · rw [show 2 ^ 256 + u0.toNat - P % 2 ^ 256 = X % D.toNat by omega,Nat.mod_eq_of_lt hR]
theorem eDecV1_le_one (mem : ByteArray) : (eDecV1 mem).toNat ≤ 1 := by
  show (UInt256.gt _ _).toNat ≤ 1
  rw [QHat.toNat_gt]
  split <;> omega
/-- The estimator facts used by both bounds of `qhatV1`. -/
theorem v1_core (mem : ByteArray) (n mm : Nat)
    (hn : 2 ≤ n) (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm) (hpre : PreOK mem) :
    (eDecV1 mem).toNat ≤ (eQ mem).toNat ∧ (eDec mem).toNat ≤ (eQ mem).toNat ∧
      ((eHi mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat →
        (eDecV1 mem).toNat ≤ (eDec mem).toNat ∧
        (eQ mem).toNat * (MachineState.readWord mem 0).toNat ≤
          (MachineState.readWord mem 2080).toNat * 2 ^ 256 + (MachineState.readWord mem 2112).toNat) := by
  obtain ⟨v,hv,hL,hmul,hdpos,hHi,hRho,raw_q,hdecval,hdecle⟩ := est_core mem n mm hn htop hmod hpre
  obtain ⟨hPL,hPD,hPX,hPB,hPI⟩ := hpre
  have hspos : (0:Nat) < 2 ^ v := Nat.two_pow_pos v
  have hshift : ∀ a : UInt256,(UInt256.shiftRight a (UInt256.ofNat 128)).toNat
      = a.toNat / 2 ^ 128 := by
    intro a
    rw [Challenge.EvmProof.Word.shiftRight_toNat a (by norm_num),Nat.shiftRight_eq_div_pow]
  have ha : (eQ mem).toNat / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact (eQ mem).val.isLt)
  have hc : (MachineState.readWord mem 32).toNat / 2 ^ 128 < 2 ^ 128 :=
    Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact (MachineState.readWord mem 32).val.isLt)
  have hcorr : (corrOf mem).toNat = (MachineState.readWord mem 32).toNat / 2 ^ 128 / 2 ^ v := by
    show (UInt256.shiftRight _ (MachineState.readWord mem PRE_L)).toNat = _
    rw [hPL,shiftRight_preK _ _ v hv hL,hshift,hL]
  have hcle : (corrOf mem).toNat ≤ (MachineState.readWord mem 32).toNat / 2 ^ 128 := by
    rw [hcorr]; exact Nat.div_le_self _ _
  have hprod : (UInt256.shiftRight (eQ mem) (UInt256.ofNat 128) * corrOf mem).toNat =
      (eQ mem).toNat / 2 ^ 128 * (corrOf mem).toNat := by
    rw [Setup.word_toNat_mul,hshift]
    apply Nat.mod_eq_of_lt
    calc (eQ mem).toNat / 2 ^ 128 * (corrOf mem).toNat
        < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' ha (lt_of_le_of_lt hcle hc)
      _ = 2 ^ 256 := by rw [← pow_add]
  have hdecV1val : (eDecV1 mem).toNat =
      if (eRho mem).toNat < (eQ mem).toNat / 2 ^ 128 * (corrOf mem).toNat then 1 else 0 := by
    show (UInt256.gt _ _).toNat = _
    rw [QHat.toNat_gt,hprod]
  have hV1le : (eDecV1 mem).toNat ≤ (eQ mem).toNat := by
    rw [hdecV1val]
    split
    · rename_i hlt
      rcases Nat.eq_zero_or_pos ((eQ mem).toNat / 2 ^ 128) with h0 | hp
      · rw [h0,Nat.zero_mul] at hlt; omega
      · have hle := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 128)).mp hp
        have h128 : (1:Nat) ≤ 2 ^ 128 := Nat.one_le_two_pow
        omega
    · omega
  refine ⟨hV1le,hdecle,fun hs => ⟨?_,?_⟩⟩
  · -- a decrement taken by the pre-shifted test is taken by the full test
    have hq := raw_q hs
    have hDpos : 0 < (MachineState.readWord mem 0).toNat := by rw [← hmul]; positivity
    have hr := rhat_toNat (MachineState.readWord mem 2080) (MachineState.readWord mem 2112)
      (MachineState.readWord mem 0) (eQ mem) hDpos hq
    rw [hdecV1val,hdecval,hr]
    split
    · rename_i hlt
      -- X mod D = X mod 2^v + 2^v * rho < 2^v * (rho + 1) ≤ a * (2^v * c') ≤ a * c
      have hsplit : ((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
          (MachineState.readWord mem 2112).toNat) % (MachineState.readWord mem 0).toNat =
          ((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
            (MachineState.readWord mem 2112).toNat) % 2 ^ v + 2 ^ v * (eRho mem).toNat := by
        rw [← hmul,Nat.mod_mul,hRho]
      have hlow := Nat.mod_lt ((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
            (MachineState.readWord mem 2112).toNat) hspos
      have h1 : 2 ^ v * ((eRho mem).toNat + 1) ≤
          2 ^ v * ((eQ mem).toNat / 2 ^ 128 * (corrOf mem).toNat) :=
        Nat.mul_le_mul_left _ hlt
      have h2 : 2 ^ v * ((eQ mem).toNat / 2 ^ 128 * (corrOf mem).toNat) ≤
          (eQ mem).toNat / 2 ^ 128 * ((MachineState.readWord mem 32).toNat / 2 ^ 128) := by
        rw [Nat.mul_left_comm]
        apply Nat.mul_le_mul_left
        rw [hcorr,Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
      rw [if_pos (by rw [hsplit]; nlinarith)]
    · exact Nat.zero_le _
  · rw [raw_q hs]
    exact Nat.div_mul_le_self _ _
theorem qhatV1_toNat (mem : ByteArray) (hdec : (eDecV1 mem).toNat ≤ (eQ mem).toNat) :
    (qhatV1 mem).toNat =
      if (eHi mem).toNat < (MachineState.readWord mem PRE_DODD).toNat
      then (eQ mem).toNat - (eDecV1 mem).toNat else 2 ^ 256 - 1 :=
  sat_select_toNat _ _ _ _ hdec
theorem qhatOf_toNat' (mem : ByteArray) (hdec : (eDec mem).toNat ≤ (eQ mem).toNat) :
    (qhatOf mem).toNat =
      if (eHi mem).toNat < (MachineState.readWord mem PRE_DODD).toNat
      then (eQ mem).toNat - (eDec mem).toNat else 2 ^ 256 - 1 := by
  rw [qhatOf_eq]; exact sat_select_toNat _ _ _ _ hdec
theorem qhatV1_ge (mem : ByteArray) (n mm u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hpre : PreOK mem) (htv : tv mem n = u) (hu : u < mm * Limbs.radix) :
    u / mm ≤ (qhatV1 mem).toNat := by
  have hge := qhatOf_ge mem n mm u hn hn32 htop hmod hpre htv hu
  obtain ⟨hV1,hdec,hns⟩ := v1_core mem n mm hn htop hmod hpre
  have hPD := hpre.2.1
  rw [qhatOf_toNat' mem hdec] at hge
  rw [qhatV1_toNat mem hV1]
  split
  · rename_i hs
    rw [if_pos hs] at hge
    have := (hns (by rw [← hPD]; exact hs)).1
    omega
  · rename_i hs
    rw [if_neg hs] at hge
    exact hge
theorem qhatV1_top_mul_le (mem : ByteArray) (n mm u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hpre : PreOK mem) (htv : tv mem n = u) (hu : u < mm * Limbs.radix) :
    (qhatV1 mem).toNat * (MachineState.readWord mem 0).toNat ≤
      (MachineState.readWord mem 2080).toNat * 2^256 + (MachineState.readWord mem 2112).toNat := by
  have hold := qhat_top_mul_le mem n mm u hn hn32 htop hmod hpre htv hu
  obtain ⟨hV1,hdec,hns⟩ := v1_core mem n mm hn htop hmod hpre
  have hPD := hpre.2.1
  rw [qhatOf_toNat' mem hdec] at hold
  rw [qhatV1_toNat mem hV1]
  split
  · rename_i hs
    have hq := (hns (by rw [← hPD]; exact hs)).2
    exact (Nat.mul_le_mul_right _ (Nat.sub_le _ _)).trans hq
  · rename_i hs
    rw [if_neg hs] at hold
    exact hold
/-! ## The conversion step with `qhatV1` (copies of the `qhatOf` step lemmas; they use the
estimate only through `qhatV1_ge` and `qhatV1_top_mul_le`) -/
def stepMemV1 (mem : ByteArray) (n mm : Nat) : ByteArray :=
  let um := uMem mem n
  let q := qhatV1 um
  let mac := macOf um n q
  let mid := midMem mac.memory mac.carry q
  let neg := negOf mac.memory mac.carry q
  fixMem mid n mm neg
def stepMemsV1 (mem : ByteArray) (n mm : Nat) : Nat → ByteArray
  | 0 => mem
  | k + 1 => stepMemV1 (stepMemsV1 mem n mm k) n mm
theorem stepMemV1_readWord_disjoint (mem : ByteArray) (n mm addr : Nat) (hn : 1 ≤ n)
    (hdisj : (addr + 32 ≤ 512 ∨ 512 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr) ∧
      (addr + 32 ≤ 2080 ∨ 2112 + 32 * n ≤ addr)) :
    MachineState.readWord (stepMemV1 mem n mm) addr = MachineState.readWord mem addr := by
  unfold stepMemV1
  simp only
  rw [fixMem_readWord_disjoint _ n mm _ addr hdisj.2.2]
  show MachineState.readWord (Exp.storeWord _ 2080 _) addr = _
  unfold Exp.storeWord
  rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
  rw [mac_readWord_disjoint _ n addr _ hn (by omega)]
  exact uMem_readWord_disjoint mem n addr hdisj.2.2
theorem fastRepresents_stepMemV1 (mem : ByteArray) (n mm ptr cnt v : Nat) (hn : 1 ≤ n)
    (hdisj : (ptr + 32 * cnt ≤ 512 ∨ 512 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 1792 ∨ 1792 + 32 * n ≤ ptr) ∧
      (ptr + 32 * cnt ≤ 2080 ∨ 2112 + 32 * n ≤ ptr))
    (hrep : Model.FastRepresents mem ptr cnt v) :
    Model.FastRepresents (stepMemV1 mem n mm) ptr cnt v := by
  refine (Model.fastRepresents_congr ?_ v).2 hrep
  intro i hi
  exact stepMemV1_readWord_disjoint mem n mm _ hn (by omega)
theorem mid_neg_tn_zeroV1 (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem)
    (h0 : negOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
            (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry
            (qhatV1 (uMem mem n)) = UInt256.ofNat 0) :
    tnOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry
        (qhatV1 (uMem mem n)) = UInt256.ofNat 0 := by
  have hmodU : Model.FastRepresents (uMem mem n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by omega))
  have hnegU : Model.FastRepresents (uMem mem n) NEG n (Limbs.radix ^ n - mm) := by
    refine (Model.fastRepresents_congr ?_ _).2 hneg
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by unfold NEG; omega))
  have hu : tv (uMem mem n) n = r * Limbs.radix := uMem_tv mem n r hn hn32 hbase
  have hulo : r * Limbs.radix < Limbs.radix ^ (n + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_right (lt_trans hr hmm) Limbs.radix_pos
  obtain ⟨hrel,hltmid,hneg1⟩ :=
    mid_relation (uMem mem n) n mm (qhatV1 (uMem mem n)) (r * Limbs.radix) hn hn32 hmm hmodU
      hnegU hu hulo
  have hqge : (r * Limbs.radix) / mm ≤ (qhatV1 (uMem mem n)).toNat :=
    qhatV1_ge (uMem mem n) n mm (r * Limbs.radix) hn hn32 htop hmodU
      (PreOK_uMem mem n hn32 hpre) hu
      (Nat.mul_lt_mul_of_pos_right hr Limbs.radix_pos)
  have h0' : (negOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))).toNat = 0 := by
    rw [h0] <;> decide
  rw [h0',Nat.zero_mul,Nat.add_zero] at hrel
  obtain ⟨Q,hQ⟩ : ∃ Q,(qhatV1 (uMem mem n)).toNat = Q := ⟨_,rfl⟩
  rw [hQ] at hrel hqge
  have hdm := Nat.div_add_mod' (r * Limbs.radix) mm
  have hmodlt := Nat.mod_lt (r * Limbs.radix) hmpos
  have htv : tv (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) n < mm := by
    by_cases hQD : Q ≤ (r * Limbs.radix) / mm
    · have hqeq : Q = (r * Limbs.radix) / mm := by omega
      rw [hqeq] at hrel
      omega
    · have hle : (r * Limbs.radix) / mm + 1 ≤ Q := by omega
      have hstep : ((r * Limbs.radix) / mm + 1) * mm ≤ Q * mm :=
        Nat.mul_le_mul_right mm hle
      have hmul : (r * Limbs.radix) / mm * mm + mm ≤ Q * mm := by
        have h1 : ((r * Limbs.radix) / mm + 1) * mm =
            (r * Limbs.radix) / mm * mm + mm := by rw [Nat.add_mul,Nat.one_mul]
        omega
      omega
  have htn := tn_zero_of_lt (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
    (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) n
    (lt_trans htv hmm)
  have hrd : MachineState.readWord (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) 2080 =
      tnOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n)) := by
    unfold midMem Exp.storeWord tnOf wN
    rw [Challenge.EvmProof.Memory.readWord_writeWord]
  rw [← hrd]
  exact Challenge.EvmProof.Word.word_ext (htn.trans (by decide))
theorem step_specV1 (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    RepairFacts
      (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n)))
      n mm
      (negOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) ∧
    Model.FastRepresents (stepMemV1 mem n mm) 2112 n (r * Limbs.radix % mm) := by
  have hmodU : Model.FastRepresents (uMem mem n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by omega))
  have hnegU : Model.FastRepresents (uMem mem n) NEG n (Limbs.radix ^ n - mm) := by
    refine (Model.fastRepresents_congr ?_ _).2 hneg
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by unfold NEG; omega))
  have hu : tv (uMem mem n) n = r * Limbs.radix := uMem_tv mem n r hn hn32 hbase
  have hulo : r * Limbs.radix < Limbs.radix ^ (n + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_right (lt_trans hr hmm) Limbs.radix_pos
  obtain ⟨hrel,hltmid,hneg1⟩ :=
    mid_relation (uMem mem n) n mm (qhatV1 (uMem mem n)) (r * Limbs.radix) hn hn32 hmm hmodU
      hnegU hu hulo
  have hmodMid : Model.FastRepresents
      (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmodU
    intro i hi
    show MachineState.readWord (Exp.storeWord _ 2080 _) _ = _
    unfold Exp.storeWord
    rw [Csub.readWord_write_disjoint _ _ _ _ (by omega)]
    exact mac_readWord_disjoint (uMem mem n) n _ _ (by omega) (Or.inl (by omega))
  obtain ⟨rf,hcong,hltP,htn⟩ :=
    repair_spec _ n mm _ (r * Limbs.radix) (qhatV1 (uMem mem n)).toNat (by omega) hn32 hmpos hmm
      hmodMid hrel hltmid hneg1
  refine ⟨rf,?_⟩
  show Model.FastRepresents (fixMem
    (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) n mm
    (negOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))))
    2112 n (r * Limbs.radix % mm)
  set fix := fixMem
    (midMem (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) n mm
    (negOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
      (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry (qhatV1 (uMem mem n))) with hfixv
  have hlowFix : Model.FastRepresents fix 2112 n (Csub.lowValue fix 2112 n n) :=
    Csub.fastRepresents_lowValue _ _ _
  have htvFix : tv fix n = Csub.lowValue fix 2112 n n := by
    rw [tv_def,htn]; simp
  -- the estimate never under-shoots, so the repair lands strictly below the modulus
  have hqge : (r * Limbs.radix) / mm ≤ (qhatV1 (uMem mem n)).toNat :=
    qhatV1_ge (uMem mem n) n mm (r * Limbs.radix) hn hn32 htop hmodU
      (PreOK_uMem mem n hn32 hpre) hu
      (Nat.mul_lt_mul_of_pos_right hr Limbs.radix_pos)
  have hltmm : tv fix n < mm := by
    rw [hfixv]
    exact repair_lt_mm _ n mm _ (r * Limbs.radix) (qhatV1 (uMem mem n)).toNat
      (by omega) hn32 hmpos hmm hmodMid hrel hltmid hneg1 hqge
  have heq : Csub.lowValue fix 2112 n n = r * Limbs.radix % mm := by
    rw [← htvFix,← hcong,Nat.mod_eq_of_lt hltmm]
  rw [heq] at hlowFix
  exact hlowFix
theorem stepMemV1_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    Model.FastRepresents (stepMemV1 mem n mm) 2112 n (r * Limbs.radix % mm) :=
  (step_specV1 mem n mm r hn hn32 hmpos hmm htop hmod hneg hbase hr hpre).2
theorem stepMemsV1_modulus (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hmod : Model.FastRepresents mem 0 n mm) :
    ∀ k,Model.FastRepresents (stepMemsV1 mem n mm k) 0 n mm := by
  intro k
  induction k with
  | zero => exact hmod
  | succ k ih =>
      exact fastRepresents_stepMemV1 _ n mm 0 n mm hn
        ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩ ih
theorem stepMemsV1_neg (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm)) :
    ∀ k,Model.FastRepresents (stepMemsV1 mem n mm k) NEG n (Limbs.radix ^ n - mm) := by
  intro k
  induction k with
  | zero => exact hneg
  | succ k ih =>
      exact fastRepresents_stepMemV1 _ n mm NEG n _ hn
        ⟨Or.inr (by unfold NEG; omega),Or.inl (by unfold NEG; omega),
          Or.inl (by unfold NEG; omega)⟩ ih
theorem PreOK_stepMemV1 (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (h : PreOK mem) : PreOK (stepMemV1 mem n mm) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := h
  have hz : MachineState.readWord (stepMemV1 mem n mm) 0 = MachineState.readWord mem 0 :=
    stepMemV1_readWord_disjoint mem n mm 0 hn
      ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [stepMemV1_readWord_disjoint mem n mm PRE_L hn
      ⟨Or.inr (by simp only [PRE_L]; omega),Or.inl (by simp only [PRE_L]; omega),
        Or.inl (by simp only [PRE_L]; omega)⟩,hz]
    exact h1
  · rw [stepMemV1_readWord_disjoint mem n mm PRE_DODD hn
      ⟨Or.inr (by simp only [PRE_DODD]; omega),Or.inl (by simp only [PRE_DODD]; omega),
        Or.inl (by simp only [PRE_DODD]; omega)⟩,hz]
    exact h2
  · rw [stepMemV1_readWord_disjoint mem n mm PRE_X hn
      ⟨Or.inr (by simp only [PRE_X]; omega),Or.inl (by simp only [PRE_X]; omega),
        Or.inl (by simp only [PRE_X]; omega)⟩,hz]
    exact h3
  · rw [stepMemV1_readWord_disjoint mem n mm PRE_BMOD hn
      ⟨Or.inr (by simp only [PRE_BMOD]; omega),Or.inl (by simp only [PRE_BMOD]; omega),
        Or.inl (by simp only [PRE_BMOD]; omega)⟩,hz]
    exact h4
  · rw [stepMemV1_readWord_disjoint mem n mm PRE_DINV hn
      ⟨Or.inr (by simp only [PRE_DINV]; omega),Or.inl (by simp only [PRE_DINV]; omega),
        Or.inl (by simp only [PRE_DINV]; omega)⟩,hz]
    exact h5
theorem PreOK_stepMemsV1 (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8)
    (h : PreOK mem) : ∀ k,PreOK (stepMemsV1 mem n mm k) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact PreOK_stepMemV1 _ n mm hn hn32 ih
theorem stepMemsV1_represents (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem) :
    ∀ k,Model.FastRepresents (stepMemsV1 mem n mm k) 2112 n (r * Limbs.radix ^ k % mm) := by
  intro k
  induction k with
  | zero =>
      simp only [stepMemsV1,pow_zero,Nat.mul_one]
      rw [Nat.mod_eq_of_lt hr]; exact hbase
  | succ k ih =>
      show Model.FastRepresents (stepMemV1 (stepMemsV1 mem n mm k) n mm) 2112 n _
      have h := stepMemV1_represents (stepMemsV1 mem n mm k) n mm _ hn (by omega) hmpos hmm htop
        (stepMemsV1_modulus mem n mm (by omega) hn32 hmod k) (stepMemsV1_neg mem n mm (by omega) hn32 hneg k)
        ih (Nat.mod_lt _ hmpos) (PreOK_stepMemsV1 mem n mm (by omega) hn32 hpre k)
      have heq : r * Limbs.radix ^ k % mm * Limbs.radix % mm =
          r * Limbs.radix ^ (k + 1) % mm := by
        rw [pow_succ,← Nat.mul_assoc,Nat.mul_mod,Nat.mod_mod,← Nat.mul_mod]
      rw [← heq]
      exact h
theorem qhat_product_ltV1 (mem : ByteArray) (n mm u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (htop : Limbs.radix^n < 2*mm)
    (hmod : Model.FastRepresents mem 0 n mm) (hpre : PreOK mem)
    (htv : tv mem n=u) (hu : u<mm*Limbs.radix) :
    (qhatV1 mem).toNat*mm < u+Limbs.radix^n := by
  have hp : 0<Limbs.radix^(n-1) := Nat.pow_pos Limbs.radix_pos
  have hRn : Limbs.radix^(n-1)*Limbs.radix=Limbs.radix^n := by
    rw [←pow_succ]; congr 1; omega
  have hfit : mm/Limbs.radix^(n-1)<Limbs.radix :=
    Nat.div_lt_of_lt_mul (by rw [hRn]; exact hmod.1)
  have h0 := Model.readWord_of_fastRepresents hmod (j:=0) (by omega)
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one,Nat.zero_add] at h0
  rw [show n-1-0=n-1 by omega,Nat.mod_eq_of_lt hfit] at h0
  have split : (MachineState.readWord mem 0).toNat*Limbs.radix^(n-1)+
      mm%Limbs.radix^(n-1)=mm := by
    rw [h0]; exact Nat.div_add_mod' _ _
  have low := Csub.lowValue_succ mem 2112 n (n-1)
  rw [show n-1+1=n by omega] at low
  rw [show n-1-(n-1)=0 by omega,Nat.mul_zero,Nat.add_zero] at low
  have top_u : ((MachineState.readWord mem 2080).toNat*Limbs.radix+
      (MachineState.readWord mem 2112).toNat)*Limbs.radix^(n-1) ≤ u := by
    rw [←htv,tv_def,low,←hRn]
    nlinarith
  have top_q := qhatV1_top_mul_le mem n mm u hn hn32 htop hmod hpre htv hu
  change (qhatV1 mem).toNat*(MachineState.readWord mem 0).toNat ≤
    (MachineState.readWord mem 2080).toNat*Limbs.radix+(MachineState.readWord mem 2112).toNat at top_q
  have first := (Nat.mul_le_mul_right (Limbs.radix^(n-1)) top_q).trans top_u
  have small := Nat.mul_lt_mul'' (show (qhatV1 mem).toNat<Limbs.radix from (qhatV1 mem).val.isLt)
    (Nat.mod_lt mm hp)
  have eqprod : (qhatV1 mem).toNat*mm =
      (qhatV1 mem).toNat*(MachineState.readWord mem 0).toNat*Limbs.radix^(n-1)+
      (qhatV1 mem).toNat*(mm%Limbs.radix^(n-1)) := by
    conv_lhs => rw [←split]
    ring
  have total := Nat.add_lt_add_of_le_of_lt first small
  rw [Nat.mul_comm Limbs.radix (Limbs.radix^(n-1)),hRn] at total
  rw [eqprod]
  exact total
theorem mid_neg_tn_maxV1 (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem)
    (h0 : negOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
            (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry
            (qhatV1 (uMem mem n)) = UInt256.ofNat 1) :
    tnOf (macOf (uMem mem n) n (qhatV1 (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatV1 (uMem mem n))).carry
        (qhatV1 (uMem mem n)) = Monpro.maxWord := by
  have hmodU : Model.FastRepresents (uMem mem n) 0 n mm := by
    refine (Model.fastRepresents_congr ?_ mm).2 hmod
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by omega))
  have hnegU : Model.FastRepresents (uMem mem n) NEG n (Limbs.radix ^ n - mm) := by
    refine (Model.fastRepresents_congr ?_ _).2 hneg
    intro i hi
    exact uMem_readWord_disjoint mem n _ (Or.inl (by unfold NEG; omega))
  have hu : tv (uMem mem n) n = r * Limbs.radix := uMem_tv mem n r hn hn32 hbase
  have hulo : r * Limbs.radix < Limbs.radix ^ (n + 1) := by
    rw [pow_succ]
    exact Nat.mul_lt_mul_of_pos_right (lt_trans hr hmm) Limbs.radix_pos
  obtain ⟨hrel,hltmid,hneg1⟩ :=
    mid_relation (uMem mem n) n mm (qhatV1 (uMem mem n)) (r * Limbs.radix) hn hn32 hmm hmodU
      hnegU hu hulo
  let um := uMem mem n
  let q := qhatV1 um
  let mac := macOf um n q
  let mid := midMem mac.memory mac.carry q
  let t := tnOf mac.memory mac.carry q
  let C := Limbs.radix^n
  let L := Csub.lowValue mid 2112 n n
  have prod : q.toNat*mm < r*Limbs.radix+C :=
    qhat_product_ltV1 um n mm (r*Limbs.radix) hn hn32 htop hmodU
      (PreOK_uMem mem n hn32 hpre) hu
      (Nat.mul_lt_mul_of_pos_right hr Limbs.radix_pos)
  have sign : (negOf mac.memory mac.carry q).toNat=1 := by
    rw [h0]; decide
  have rd : MachineState.readWord mid 2080=t := by
    dsimp [mid,t]
    unfold midMem Exp.storeWord tnOf wN
    rw [Challenge.EvmProof.Memory.readWord_writeWord]
  change r*Limbs.radix+(negOf mac.memory mac.carry q).toNat*Limbs.radix^(n+1)=
    q.toNat*mm+tv mid n at hrel
  rw [sign,Nat.one_mul,tv_def,rd,pow_succ] at hrel
  change r*Limbs.radix+C*Limbs.radix=q.toNat*mm+(t.toNat*C+L) at hrel
  have rel : r*Limbs.radix+Limbs.radix*C=q.toNat*mm+(t.toNat*C+L) := by
    simpa only [Nat.mul_comm C Limbs.radix] using hrel
  have tl : t.toNat<Limbs.radix := t.val.isLt
  have ll : L<C := Csub.lowValue_lt _ _ _ _
  have mx : Monpro.maxWord.toNat=Limbs.radix-1 := by decide
  change t=Monpro.maxWord
  apply Challenge.EvmProof.Word.word_ext
  rw [mx]
  by_contra ne
  have small : t.toNat+1 ≤ Limbs.radix-1 := by omega
  have tvsmall : t.toNat*C+L < (Limbs.radix-1)*C := calc
    t.toNat*C+L < t.toNat*C+C := Nat.add_lt_add_left ll _
    _ = (t.toNat+1)*C := by ring
    _ ≤ (Limbs.radix-1)*C := Nat.mul_le_mul_right _ small
  have sum := Nat.add_lt_add prod tvsmall
  have hb : Limbs.radix-1+1=Limbs.radix := Nat.sub_add_cancel (by have := Limbs.radix_pos; omega)
  have eq : (r*Limbs.radix+C)+(Limbs.radix-1)*C=r*Limbs.radix+Limbs.radix*C := calc
    (r*Limbs.radix+C)+(Limbs.radix-1)*C = r*Limbs.radix+(Limbs.radix-1+1)*C := by ring
    _ = r*Limbs.radix+Limbs.radix*C := by rw [hb]
  rw [eq,←rel] at sum
  exact Nat.lt_irrefl _ sum
end Challenge.Modexp.Submission.Proofs.Fast.Shift
