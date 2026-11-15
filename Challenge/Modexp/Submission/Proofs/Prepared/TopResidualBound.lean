import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Challenge.Modexp.Submission.Proofs.Fast.Shift
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs Challenge.Modexp.Submission.Proofs.Fast
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast.QHat
theorem qhat_top_mul_le (mem : ByteArray) (n mm u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hpre : PreOK mem) (htv : tv mem n = u) (hu : u < mm * Limbs.radix) :
    (qhatOf mem).toNat * (MachineState.readWord mem 0).toNat ≤
      (MachineState.readWord mem 2080).toNat * 2^256 + (MachineState.readWord mem 2112).toNat := by
  obtain ⟨hPL,hPD,hPX,hPB,hPI⟩ := hpre
  have hR : Limbs.radix = 2 ^ 256 := rfl
  have hDne := top_limb_ne_zero mem n mm hn htop hmod
  obtain ⟨v,hv,hL,hmul,hodd,hdpos,hbmod,hXd⟩ :=
    pre_facts (MachineState.readWord mem 0) hDne
  have hmpos : 0 < mm := by omega
  -- abbreviations
  have hspos : (0:Nat) < 2 ^ v := Nat.two_pow_pos v
  have hsdvd : (2:Nat) ^ v ∣ 2 ^ 256 := pow_dvd_pow 2 (by omega)
  have hst : (2:Nat) ^ v * (2 ^ 256 / 2 ^ v) = 2 ^ 256 := Nat.mul_div_cancel' hsdvd
  have htpos : 0 < (2:Nat) ^ 256 / 2 ^ v := by
    rcases Nat.eq_zero_or_pos (2 ^ 256 / 2 ^ v) with h | h
    · rw [h,Nat.mul_zero] at hst; norm_num at hst
    · exact h
  -- the estimator's low word
  have hHi : (eHi mem).toNat = (MachineState.readWord mem 2080).toNat / 2 ^ v := by
    rw [eHi_toNat mem hPL hDne,hL]
  have hLwlt : (MachineState.readWord mem 2112).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 2112).val.isLt
  have hHlt : (MachineState.readWord mem 2080).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 2080).val.isLt
  have hlorw : (MachineState.readWord mem 2112).toNat / 2 ^ v +
      (2 ^ 256 / 2 ^ v) * ((MachineState.readWord mem 2080).toNat % 2 ^ v) < 2 ^ 256 := by
    have h1 : (MachineState.readWord mem 2112).toNat / 2 ^ v < 2 ^ 256 / 2 ^ v := by
      apply Nat.div_lt_div_of_lt_of_dvd hsdvd hLwlt
    have h2 : (MachineState.readWord mem 2080).toNat % 2 ^ v < 2 ^ v := Nat.mod_lt _ hspos
    have h3 : (2 ^ 256 / 2 ^ v) * ((MachineState.readWord mem 2080).toNat % 2 ^ v)
        ≤ (2 ^ 256 / 2 ^ v) * (2 ^ v - 1) := Nat.mul_le_mul_left _ (by omega)
    have h4 : (2 ^ 256 / 2 ^ v) * (2 ^ v - 1) = 2 ^ 256 - 2 ^ 256 / 2 ^ v := by
      rw [Nat.mul_sub,Nat.mul_one,Nat.mul_comm,hst]
    have h5 : 2 ^ 256 / 2 ^ v ≤ 2 ^ 256 := Nat.div_le_self _ _
    omega
  have hLo : (eLo mem).toNat =
      (2 ^ 256 / 2 ^ v) * ((MachineState.readWord mem 2080).toNat % 2 ^ v) +
        (MachineState.readWord mem 2112).toNat / 2 ^ v := by
    rw [eLo_toNat mem hPL hPX hDne,hL]
    rcases hXd with hX1 | ⟨hv1,hX0⟩
    · have hXt : (preX (MachineState.readWord mem 0)).toNat = 2 ^ 256 / 2 ^ v :=
        Nat.eq_of_mul_eq_mul_left hspos (by rw [hX1,hst])
      rw [hXt,QHat.mul_shift_mod (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
        (MachineState.readWord mem 2080).toNat hspos htpos hst]
      rw [Nat.mod_eq_of_lt (by
        have := hlorw
        omega)]
      omega
    · rw [hX0,Nat.zero_mul,Nat.zero_mod]
      have hv0 : v = 0 := by
        by_contra hc
        have : (2:Nat) ^ 1 ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      subst hv0
      simp only [pow_zero,Nat.div_one,Nat.mod_one,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
      exact Nat.mod_eq_of_lt hLwlt
  -- the shifted two-word value
  have hsplit := QHat.shift_split (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
      (MachineState.readWord mem 2080).toNat (MachineState.readWord mem 2112).toNat hspos hst
  have hRho : (eRho mem).toNat =
      (((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
        (MachineState.readWord mem 2112).toNat) / 2 ^ v)
        % (preDodd (MachineState.readWord mem 0)).toNat := by
    rw [eRho_toNat mem hPL hPD hPB (by omega),hHi,hbmod,hLo,← hsplit]
    have hcong : (MachineState.readWord mem 2080).toNat / 2 ^ v *
        (2 ^ 256 % (preDodd (MachineState.readWord mem 0)).toNat)
        ≡ (MachineState.readWord mem 2080).toNat / 2 ^ v * 2 ^ 256
          [MOD (preDodd (MachineState.readWord mem 0)).toNat] :=
      Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
    clear hcong
    rw [Nat.add_mod,Nat.add_mod ((MachineState.readWord mem 2080).toNat / 2 ^ v * 2 ^ 256)]
    congr 2
    simp [Nat.mul_mod]
  -- bounds on rho
  have hDlt : (MachineState.readWord mem 0).toNat < 2 ^ 256 :=
    (MachineState.readWord mem 0).val.isLt
  have hdoddle : (preDodd (MachineState.readWord mem 0)).toNat ≤
      (MachineState.readWord mem 0).toNat := by
    rw [← hmul]; exact Nat.le_mul_of_pos_left _ hspos
  have hrholt : (eRho mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat := by
    rw [hRho]; exact Nat.mod_lt _ hdpos
  -- the word difference
  have hDiff : (eDiff mem).toNat ≡
      (eLo mem).toNat + (2 ^ 256 - (eRho mem).toNat) [MOD 2 ^ 256] := by
    rw [eDiff_toNat]
    have heq : 2 ^ 256 + (eLo mem).toNat - (eRho mem).toNat
        = (eLo mem).toNat + (2 ^ 256 - (eRho mem).toNat) := by omega
    rw [heq]
    exact Nat.mod_modEq _ _
  have hQval : (eQ mem).toNat =
      (preDinv (MachineState.readWord mem 0)).toNat * (eDiff mem).toNat % 2 ^ 256 :=
    eQ_toNat mem hPI
  -- the truncated-product test, in Nat
  have hshift : ∀ a : UInt256,(UInt256.shiftRight a (UInt256.ofNat 128)).toNat
      = a.toNat / 2 ^ 128 := by
    intro a
    rw [Challenge.EvmProof.Word.shiftRight_toNat a (by norm_num),Nat.shiftRight_eq_div_pow]
  have hprod : ((UInt256.shiftRight (eQ mem) (UInt256.ofNat 128) *
      UInt256.shiftRight (MachineState.readWord mem 32) (UInt256.ofNat 128)).toNat)
      = ((eQ mem).toNat / 2 ^ 128) * ((MachineState.readWord mem 32).toNat / 2 ^ 128) := by
    rw [Setup.word_toNat_mul,hshift,hshift]
    apply Nat.mod_eq_of_lt
    have h1 : (eQ mem).toNat / 2 ^ 128 < 2 ^ 128 :=
      Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact (eQ mem).val.isLt)
    have h2 : (MachineState.readWord mem 32).toNat / 2 ^ 128 < 2 ^ 128 :=
      Nat.div_lt_of_lt_mul (by rw [← pow_add]; exact (MachineState.readWord mem 32).val.isLt)
    calc (eQ mem).toNat / 2 ^ 128 * ((MachineState.readWord mem 32).toNat / 2 ^ 128)
        < 2 ^ 128 * 2 ^ 128 := Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ 256 := by rw [← pow_add]
  have hdecval : (eDec mem).toNat =
      if (MachineState.readWord mem 2112 - MachineState.readWord mem 0 * eQ mem).toNat <
        ((eQ mem).toNat / 2 ^ 128) * ((MachineState.readWord mem 32).toNat / 2 ^ 128)
      then 1 else 0 := by
    show (UInt256.gt _ _).toNat = _
    rw [QHat.toNat_gt,hprod]
  have hdec1 : (eDec mem).toNat = 1 → 2 ^ 128 ≤ (eQ mem).toNat := by
    intro h1
    rw [hdecval] at h1
    split at h1
    · rename_i hlt
      rcases Nat.eq_zero_or_pos ((eQ mem).toNat / 2 ^ 128) with h0 | hp
      · rw [h0,Nat.zero_mul] at hlt; omega
      · have hle := (Nat.le_div_iff_mul_le (Nat.two_pow_pos 128)).mp hp
        omega
    · omega
  have raw_q : (eHi mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat →
      (eQ mem).toNat = ((MachineState.readWord mem 2080).toNat * 2^256 +
        (MachineState.readWord mem 2112).toNat) / (MachineState.readWord mem 0).toNat := by
    intro hsat
    rw [hHi] at hsat
    have hraw : (eQ mem).toNat =
        ((MachineState.readWord mem 2080).toNat * 2 ^ 256 +
          (MachineState.readWord mem 2112).toNat) / (MachineState.readWord mem 0).toNat := by
      rw [hQval]
      exact QHat.est_raw (2 ^ 256) (2 ^ v) (2 ^ 256 / 2 ^ v)
        (preDodd (MachineState.readWord mem 0)).toNat (MachineState.readWord mem 0).toNat
        (MachineState.readWord mem 2080).toNat (MachineState.readWord mem 2112).toNat
        (eRho mem).toNat (eDiff mem).toNat (preDinv (MachineState.readWord mem 0)).toNat
        hspos htpos hst hmul hdpos hHlt hLwlt hDlt hsat hRho (by rw [← hLo]; exact hDiff)
        (preDinv_inv (MachineState.readWord mem 0) hodd)
    exact hraw
  have hdecle : (eDec mem).toNat ≤ (eQ mem).toNat := by
    have h1 := eDec_le_one mem
    rcases Nat.lt_or_ge (eDec mem).toNat 1 with h | h
    · omega
    · have := hdec1 (by omega)
      have h128 : (1:Nat) ≤ 2 ^ 128 := Nat.one_le_two_pow
      omega
  by_cases hs : (eHi mem).toNat < (preDodd (MachineState.readWord mem 0)).toNat
  · have hb := qhatOf_branch mem hPD hdecle
    rw [if_pos hs] at hb
    have hle : (qhatOf mem).toNat ≤ (eQ mem).toNat := by omega
    rw [raw_q hs] at hle
    exact (Nat.mul_le_mul_right _ hle).trans (Nat.div_mul_le_self _ _)
  · have hdle : (preDodd (MachineState.readWord mem 0)).toNat ≤
        (MachineState.readWord mem 2080).toNat / 2^v := by
      rw [hHi] at hs
      exact Nat.le_of_not_gt hs
    have htop_le : (MachineState.readWord mem 0).toNat ≤ (MachineState.readWord mem 2080).toNat := by
      have hh := (Nat.le_div_iff_mul_le hspos).mp hdle
      rw [Nat.mul_comm,hmul] at hh
      exact hh
    calc (qhatOf mem).toNat * (MachineState.readWord mem 0).toNat
        ≤ (2^256) * (MachineState.readWord mem 0).toNat :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt (qhatOf mem).val.isLt)
      _ ≤ (MachineState.readWord mem 2080).toNat * 2^256 +
          (MachineState.readWord mem 2112).toNat := by nlinarith
theorem qhat_product_lt (mem : ByteArray) (n mm u : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (htop : Limbs.radix^n < 2*mm)
    (hmod : Model.FastRepresents mem 0 n mm) (hpre : PreOK mem)
    (htv : tv mem n=u) (hu : u<mm*Limbs.radix) :
    (qhatOf mem).toNat*mm < u+Limbs.radix^n := by
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
  have top_q := qhat_top_mul_le mem n mm u hn hn32 htop hmod hpre htv hu
  change (qhatOf mem).toNat*(MachineState.readWord mem 0).toNat ≤
    (MachineState.readWord mem 2080).toNat*Limbs.radix+(MachineState.readWord mem 2112).toNat at top_q
  have first := (Nat.mul_le_mul_right (Limbs.radix^(n-1)) top_q).trans top_u
  have small := Nat.mul_lt_mul'' (show (qhatOf mem).toNat<Limbs.radix from (qhatOf mem).val.isLt)
    (Nat.mod_lt mm hp)
  have eqprod : (qhatOf mem).toNat*mm =
      (qhatOf mem).toNat*(MachineState.readWord mem 0).toNat*Limbs.radix^(n-1)+
      (qhatOf mem).toNat*(mm%Limbs.radix^(n-1)) := by
    conv_lhs => rw [←split]
    ring
  have total := Nat.add_lt_add_of_le_of_lt first small
  rw [Nat.mul_comm Limbs.radix (Limbs.radix^(n-1)),hRn] at total
  rw [eqprod]
  exact total
theorem mid_neg_tn_max (mem : ByteArray) (n mm r : Nat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hmpos : 0 < mm) (hmm : mm < Limbs.radix ^ n)
    (htop : Limbs.radix ^ n < 2 * mm)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hneg : Model.FastRepresents mem NEG n (Limbs.radix ^ n - mm))
    (hbase : Model.FastRepresents mem 2112 n r) (hr : r < mm) (hpre : PreOK mem)
    (h0 : negOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
            (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry
            (qhatOf (uMem mem n)) = UInt256.ofNat 1) :
    tnOf (macOf (uMem mem n) n (qhatOf (uMem mem n))).memory
        (macOf (uMem mem n) n (qhatOf (uMem mem n))).carry
        (qhatOf (uMem mem n)) = Monpro.maxWord := by
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
    mid_relation (uMem mem n) n mm (qhatOf (uMem mem n)) (r * Limbs.radix) hn hn32 hmm hmodU
      hnegU hu hulo
  let um := uMem mem n
  let q := qhatOf um
  let mac := macOf um n q
  let mid := midMem mac.memory mac.carry q
  let t := tnOf mac.memory mac.carry q
  let C := Limbs.radix^n
  let L := Csub.lowValue mid 2112 n n
  have prod : q.toNat*mm < r*Limbs.radix+C :=
    qhat_product_lt um n mm (r*Limbs.radix) hn hn32 htop hmodU
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
