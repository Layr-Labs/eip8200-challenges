import Challenge.Modexp.Submission.Proofs.Fast.Monpro

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! The generic CIOS arithmetic also permits an A operand above its accumulator.
For n ≤ 8, row writes end at2368. The source at2368 can therefore survive every
row and the initial zeroing. These lemmas keep the original memory transformers
and arithmetic, and widen only their source-disjointness hypotheses. -/
namespace Challenge.Modexp.Submission.Proofs.Fast.StagedMonpro
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast
open Monpro

theorem readWord_writeLimb (mem : ByteArray) (w dst addr : Nat)
    (hdstLo : 2048 ≤ dst) (hdstHi : dst + 32 ≤ 2368)
    (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord
        (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded w 32) dst) addr =
      MachineState.readWord mem addr := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  omega

theorem readWord_l1Step (mem : ByteArray) (bi : UInt256) (pa n addr j : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [l1Step]
      rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]
      exact ih

theorem readWord_l2Step (mem : ByteArray) (mu c0 : UInt256) (n addr k : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (l2Step mem mu c0 n k).memory addr =
      MachineState.readWord mem addr := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [l2Step]
      rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]
      exact ih

theorem readWord_midMem1 (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (midMem1 mem c) addr = MachineState.readWord mem addr := by
  simp only [midMem1]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]

theorem readWord_midMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (midMem mem c) addr = MachineState.readWord mem addr := by
  simp only [midMem]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr,
    readWord_midMem1 _ _ _ haddr]

theorem readWord_tailMem1 (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (tailMem1 mem c) addr = MachineState.readWord mem addr := by
  simp only [tailMem1]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr]

theorem readWord_tailMem (mem : ByteArray) (c : UInt256) (addr : Nat)
    (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (tailMem mem c) addr = MachineState.readWord mem addr := by
  simp only [tailMem]
  rw [readWord_writeLimb _ _ _ _ (by omega) (by omega) haddr,
    readWord_tailMem1 _ _ _ haddr]

theorem readWord_rowMid (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (rowMid mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  simp only [rowMid, rowL1]
  rw [readWord_midMem _ _ _ haddr, readWord_l1Step _ _ _ _ _ _ hn haddr]

theorem readWord_rowMem (mem : ByteArray) (pa pb n i addr : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (rowMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  simp only [rowMem, rowL2]
  rw [readWord_tailMem _ _ _ haddr, readWord_l2Step _ _ _ _ _ _ hn haddr,
    readWord_rowMid _ _ _ _ _ _ hn haddr]

theorem readWord_rowsMem (mem : ByteArray) (pa pb n addr : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) : ∀ i,
    MachineState.readWord (rowsMem mem pa pb n i) addr =
      MachineState.readWord mem addr := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [rowsMem, readWord_rowMem _ _ _ _ _ _ hn haddr]
      exact ih

theorem readWord_mpZeroed (s : State) (mem : ByteArray) (n addr : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (mpZeroed s mem n) addr = MachineState.readWord mem addr := by
  simp only [mpZeroed]
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

theorem readWord_monpro_preserved (s : State) (memory : ByteArray)
    (pa pb n i addr : Nat) (hn : n ≤ 8)
    (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (rowsMem (mpZeroed s memory n) pa pb n i) addr =
      MachineState.readWord memory addr := by
  rw [readWord_rowsMem _ _ _ _ _ hn haddr i, readWord_mpZeroed _ _ _ _ hn haddr]

theorem fastRepresents_monpro_preserved (s : State) (memory : ByteArray)
    (pa pb n i ptr count value : Nat) (hn : n ≤ 8)
    (hfit : ptr + 32 * count ≤ 2048 ∨ 2368 ≤ ptr)
    (hrep : Model.FastRepresents memory ptr count value) :
    Model.FastRepresents (rowsMem (mpZeroed s memory n) pa pb n i) ptr count value := by
  refine (Model.fastRepresents_congr
    (a := memory) (b := rowsMem (mpZeroed s memory n) pa pb n i) ?_ value).1 hrep
  intro j hj
  rw [readWord_monpro_preserved s memory pa pb n i (ptr + 32 * j) hn (by omega)]

theorem readWord_l1Step_src (mem : ByteArray) (bi : UInt256) (pa n j addr : Nat)
    (hn : n ≤ 8) (haddr : addr + 32 ≤ 2048 ∨ 2368 ≤ addr) :
    MachineState.readWord (l1Step mem bi pa n j).memory addr =
      MachineState.readWord mem addr :=
  readWord_l1Step mem bi pa n addr j hn haddr

theorem l1Step_succ_carry (mem : ByteArray) (bi : UInt256) (pa n j : Nat)
    (hn : n ≤ 8) (hj : j < n) (hpaFit : pa + 32 * n ≤ 2048 ∨ 2368 ≤ pa) :
    (l1Step mem bi pa n (j + 1)).carry =
      macCarry (MachineState.readWord mem (pa + 32 * (n - 1 - j))) bi
        (MachineState.readWord mem (tAddr n j)) (l1Step mem bi pa n j).carry := by
  have hkeep : MachineState.readWord (l1Step mem bi pa n j).memory
      (2112 + 32 * (n - 1 - j)) =
      MachineState.readWord mem (2112 + 32 * (n - 1 - j)) :=
    readWord_l1Step_keep mem bi pa n j hj j (Nat.le_refl j)
  simp only [l1Step, tAddr]
  rw [readWord_l1Step_src mem bi pa n j (pa + 32 * (n - 1 - j)) hn (by omega), hkeep]

theorem l1Step_succ_write (mem : ByteArray) (bi : UInt256) (pa n j : Nat)
    (hn : n ≤ 8) (hj : j < n) (hpaFit : pa + 32 * n ≤ 2048 ∨ 2368 ≤ pa) :
    (l1Step mem bi pa n (j + 1)).memory =
      MachineState.writeBytes (l1Step mem bi pa n j).memory
        (Data.Bytes.natToBytesPadded (l1Val mem bi pa n j).toNat 32) (tAddr n j) := by
  have hkeep : MachineState.readWord (l1Step mem bi pa n j).memory
      (2112 + 32 * (n - 1 - j)) =
      MachineState.readWord mem (2112 + 32 * (n - 1 - j)) :=
    readWord_l1Step_keep mem bi pa n j hj j (Nat.le_refl j)
  simp only [l1Step, l1Val, tAddr]
  rw [readWord_l1Step_src mem bi pa n j (pa + 32 * (n - 1 - j)) hn (by omega), hkeep]

theorem readWord_l1Step_val (mem : ByteArray) (bi : UInt256) (pa n k : Nat)
    (hn : n ≤ 8) (hkn : k < n) (hpaFit : pa + 32 * n ≤ 2048 ∨ 2368 ≤ pa) : ∀ j, k < j → j ≤ n →
    MachineState.readWord (l1Step mem bi pa n j).memory (tAddr n k) =
      l1Val mem bi pa n k := by
  intro j
  induction j with
  | zero => intro h; exact absurd h (Nat.not_lt_zero k)
  | succ j ih =>
      intro hkj hjn
      rw [l1Step_succ_write mem bi pa n j hn (by omega) hpaFit]
      rcases Nat.lt_or_ge k j with hlt | hge
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih hlt (by omega)
        · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
          simp only [tAddr]
          omega
      · have hkeq : k = j := by omega
        subst hkeq
        exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

private theorem mac_step_alg {S T' A' L C B Wt Wa Bi R Rad : Nat}
    (hmac : B * Rad + L = Wt + Wa * Bi + C)
    (hih : S + C * R = T' + Bi * A') :
    S + L * R + B * (R * Rad) = T' + Wt * R + Bi * (A' + Wa * R) := by
  have h1 : S + L * R + B * (R * Rad) = S + (B * Rad + L) * R := by ring
  rw [h1, hmac]
  have h2 : S + (Wt + Wa * Bi + C) * R = S + C * R + (Wt + Wa * Bi) * R := by ring
  rw [h2, hih]
  ring

theorem l1_invariant (mem : ByteArray) (bi : UInt256) (pa n : Nat)
    (hn : n ≤ 8) (hpaFit : pa + 32 * n ≤ 2048 ∨ 2368 ≤ pa) : ∀ j, j ≤ n →
    limbSum (fun k => (l1Val mem bi pa n k).toNat) j +
        (l1Step mem bi pa n j).carry.toNat * Limbs.radix ^ j =
      limbSum (fun k => (MachineState.readWord mem (tAddr n k)).toNat) j +
        bi.toNat * limbSum
          (fun k => (MachineState.readWord mem (pa + 32 * (n - 1 - k))).toNat) j := by
  intro j
  induction j with
  | zero =>
      intro _
      simp [limbSum, l1Step, Challenge.EvmProof.Word.word_toNat_ofNat]
  | succ j ih =>
      intro hjn
      have hj : j < n := by omega
      have hih := ih (Nat.le_of_succ_le hjn)
      have hmac := macSpec (MachineState.readWord mem (pa + 32 * (n - 1 - j))) bi
        (MachineState.readWord mem (tAddr n j)) (l1Step mem bi pa n j).carry
      rw [limbSum_succ, limbSum_succ, limbSum_succ,
        l1Step_succ_carry mem bi pa n j hn hj hpaFit, pow_succ]
      simp only [l1Val]
      exact mac_step_alg hmac hih

theorem l1_row (mem : ByteArray) (bi : UInt256) (pa n tlow a : Nat)
    (hn : n ≤ 8) (hpaFit : pa + 32 * n ≤ 2048 ∨ 2368 ≤ pa)
    (hta : Model.FastRepresents mem pa n a)
    (htt : Model.FastRepresents mem 2112 n tlow) :
    limbSum (fun k => (l1Val mem bi pa n k).toNat) n +
        (l1Step mem bi pa n n).carry.toNat * Limbs.radix ^ n =
      tlow + bi.toNat * a := by
  have h := l1_invariant mem bi pa n hn hpaFit n (Nat.le_refl n)
  simp only [tAddr] at h
  rw [limbSum_fastRepresents hta, limbSum_fastRepresents htt] at h
  exact h

private theorem row_alg {R P tn Cn u cu Cp v cv c0 mu m0 l0 S2 St Sm L1sum mm tlow
    a bi : Nat}
    (hA : cu * R + u = tn + Cn)
    (hB : cv * R + v = u + Cp)
    (hC : c0 * R = l0 + m0 * mu)
    (hD : S2 + Cp * P = c0 + (St + mu * Sm))
    (hE : St * R + l0 = L1sum)
    (hF : Sm * R + m0 = mm)
    (hG : L1sum + Cn * (P * R) = tlow + bi * a) :
    ((cu + cv) * (P * R) + (S2 + v * P)) * R =
      tn * (P * R) + tlow + a * bi + mu * mm := by
  calc ((cu + cv) * (P * R) + (S2 + v * P)) * R
      = cu * R * (P * R) + (cv * R + v) * (P * R) + S2 * R := by ring
    _ = cu * R * (P * R) + (u + Cp) * (P * R) + S2 * R := by rw [hB]
    _ = (cu * R + u) * (P * R) + (S2 + Cp * P) * R := by ring
    _ = (tn + Cn) * (P * R) + (S2 + Cp * P) * R := by rw [hA]
    _ = (tn + Cn) * (P * R) + (c0 + (St + mu * Sm)) * R := by rw [hD]
    _ = (tn + Cn) * (P * R) + (c0 * R + (St * R + mu * (Sm * R))) := by ring
    _ = (tn + Cn) * (P * R) + ((l0 + m0 * mu) + (St * R + mu * (Sm * R))) := by
          rw [hC]
    _ = (tn + Cn) * (P * R) + ((St * R + l0) + mu * (Sm * R + m0)) := by ring
    _ = (tn + Cn) * (P * R) + (L1sum + mu * (Sm * R + m0)) := by rw [hE]
    _ = (tn + Cn) * (P * R) + (L1sum + mu * mm) := by rw [hF]
    _ = tn * (P * R) + (L1sum + Cn * (P * R)) + mu * mm := by ring
    _ = tn * (P * R) + (tlow + bi * a) + mu * mm := by rw [hG]
    _ = tn * (P * R) + tlow + a * bi + mu * mm := by ring

theorem row_equation (mem : ByteArray) (pa pb p i : Nat) (a mm tlow : Nat)
    (hn32 : p + 2 ≤ 8) (hpaFit : pa + 32 * (p + 2) ≤ 2048 ∨ 2368 ≤ pa)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ht : Model.FastRepresents mem 2112 (p + 2) tlow)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ((MachineState.readWord (rowMem mem pa pb (p + 2) i) 2080).toNat *
          Limbs.radix ^ (p + 2) +
        Csub.lowValue (rowMem mem pa pb (p + 2) i) 2112 (p + 2) (p + 2)) *
        Limbs.radix =
      (MachineState.readWord mem 2080).toNat * Limbs.radix ^ (p + 2) + tlow +
        a * (rowBi mem pb (p + 2) i).toNat +
        (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat * mm := by
  have hpow : Limbs.radix ^ (p + 2) = Limbs.radix ^ (p + 1) * Limbs.radix :=
    pow_succ Limbs.radix (p + 1)
  have hA1 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory 2080 =
      MachineState.readWord mem 2080 :=
    readWord_l1Step_low mem (rowBi mem pb (p + 2) i) pa (p + 2) 2080 (p + 2) (by omega)
  have hM0 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
      (32 * (p + 2) - 32) = MachineState.readWord mem (32 * (p + 2) - 32) :=
    readWord_l1Step_low mem (rowBi mem pb (p + 2) i) pa (p + 2)
      (32 * (p + 2) - 32) (p + 2) (by omega)
  have hMinvR : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory 2720 =
      MachineState.readWord mem 2720 :=
    readWord_l1Step mem (rowBi mem pb (p + 2) i) pa (p + 2) 2720 (p + 2) hn32
      (Or.inr (by omega))
  have hT0 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
      (2080 + 32 * (p + 2)) =
      l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0 := by
    have h := readWord_l1Step_val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0 hn32
      (by omega) hpaFit (p + 2) (by omega) (Nat.le_refl _)
    simp only [tAddr] at h
    have haddr : 2112 + 32 * (p + 2 - 1 - 0) = 2080 + 32 * (p + 2) := by omega
    rw [haddr] at h
    exact h
  have hMDtn : MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 =
      MachineState.readWord mem 2080 + (rowL1 mem pa pb (p + 2) i).carry := by
    rw [rowMid_def, readWord_midMem_tn, hA1]
  have hMDtnp : MachineState.readWord (rowMid mem pa pb (p + 2) i) 2048 =
      UInt256.lt (MachineState.readWord mem 2080 + (rowL1 mem pa pb (p + 2) i).carry)
        (rowL1 mem pa pb (p + 2) i).carry := by
    rw [rowMid_def, readWord_midMem_tnp, hA1]
  have hL2tn : MachineState.readWord (rowL2 mem pa pb (p + 2) i).memory 2080 =
      MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 :=
    readWord_l2Step_low _ _ _ (p + 2) 2080 (p + 2 - 1) (by omega)
  have hL2tnp : MachineState.readWord (rowL2 mem pa pb (p + 2) i).memory 2048 =
      MachineState.readWord (rowMid mem pa pb (p + 2) i) 2048 :=
    readWord_l2Step_low _ _ _ (p + 2) 2048 (p + 2 - 1) (by omega)
  have hcu : (UInt256.lt (MachineState.readWord mem 2080 +
      (rowL1 mem pa pb (p + 2) i).carry)
      (rowL1 mem pa pb (p + 2) i).carry).toNat ≤ 1 := by
    rw [word_toNat_lt']
    split <;> omega
  have hcv : (UInt256.lt (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 +
      (rowL2 mem pa pb (p + 2) i).carry)
      (rowL2 mem pa pb (p + 2) i).carry).toNat ≤ 1 := by
    rw [word_toNat_lt']
    split <;> omega
  have hFtn : (MachineState.readWord (rowMem mem pa pb (p + 2) i) 2080).toNat =
      (UInt256.lt (MachineState.readWord mem 2080 + (rowL1 mem pa pb (p + 2) i).carry)
        (rowL1 mem pa pb (p + 2) i).carry).toNat +
      (UInt256.lt (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 +
        (rowL2 mem pa pb (p + 2) i).carry)
        (rowL2 mem pa pb (p + 2) i).carry).toNat := by
    rw [readWord_rowMem_tn, hL2tnp, hMDtnp, hL2tn,
      Challenge.EvmProof.Word.word_toNat_add, Nat.mod_eq_of_lt (by omega)]
  have hFts : (MachineState.readWord (rowMem mem pa pb (p + 2) i) 2112).toNat =
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 +
        (rowL2 mem pa pb (p + 2) i).carry).toNat := by
    rw [readWord_rowMem_top, hL2tn]
  have hA : (UInt256.lt (MachineState.readWord mem 2080 +
        (rowL1 mem pa pb (p + 2) i).carry)
        (rowL1 mem pa pb (p + 2) i).carry).toNat * Limbs.radix +
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080).toNat =
      (MachineState.readWord mem 2080).toNat +
        (rowL1 mem pa pb (p + 2) i).carry.toNat := by
    rw [hMDtn, radix_eq]
    exact add_carry_split (MachineState.readWord mem 2080)
      (rowL1 mem pa pb (p + 2) i).carry
  have hB : (UInt256.lt (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 +
        (rowL2 mem pa pb (p + 2) i).carry)
        (rowL2 mem pa pb (p + 2) i).carry).toNat * Limbs.radix +
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080 +
        (rowL2 mem pa pb (p + 2) i).carry).toNat =
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080).toNat +
        (rowL2 mem pa pb (p + 2) i).carry.toNat := by
    rw [radix_eq]
    exact add_carry_split (MachineState.readWord (rowMid mem pa pb (p + 2) i) 2080)
      (rowL2 mem pa pb (p + 2) i).carry
  have hC : (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat * Limbs.radix =
      (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0).toNat +
        (MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat := by
    rw [radix_eq, ← hT0, ← hM0]
    exact c0_spec
      (MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory (32 * (p + 2) - 32))
      (MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory 2720)
      (MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory (2080 + 32 * (p + 2)))
      (by rw [hM0, hMinvR]; exact hminv)
  have hD0 := l2_invariant (rowMid mem pa pb (p + 2) i)
    (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2))
    (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)) (p + 2) hn32 (p + 1) (by omega)
  simp only [Nat.add_sub_cancel] at hD0
  have hD : limbSum (fun k => (l2Val (rowMid mem pa pb (p + 2) i)
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2))
          (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)) (p + 2) k).toNat)
          (p + 1) +
        (rowL2 mem pa pb (p + 2) i).carry.toNat * Limbs.radix ^ (p + 1) =
      (rowC0 (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat +
        (limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
            (2112 + 32 * (p - k))).toNat) (p + 1) +
          (rowMu (rowL1 mem pa pb (p + 2) i).memory (p + 2)).toNat *
            limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
              (32 * (p - k))).toNat) (p + 1)) := hD0
  have hstF : ∀ k, k < p + 1 →
      (MachineState.readWord (rowMid mem pa pb (p + 2) i)
        (2112 + 32 * (p - k))).toNat =
      (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) (k + 1)).toNat := by
    intro k hk
    have h1 : MachineState.readWord (rowMid mem pa pb (p + 2) i)
        (2112 + 32 * (p - k)) =
        MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
          (2112 + 32 * (p - k)) := by
      rw [rowMid_def]
      exact readWord_midMem_high _ _ _ (by omega)
    have h2 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
        (2112 + 32 * (p - k)) =
        l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) (k + 1) := by
      have h3 := readWord_l1Step_val mem (rowBi mem pb (p + 2) i) pa (p + 2) (k + 1)
        hn32 (by omega) hpaFit (p + 2) (by omega) (Nat.le_refl _)
      simp only [tAddr] at h3
      have haddr : 2112 + 32 * (p + 2 - 1 - (k + 1)) = 2112 + 32 * (p - k) := by omega
      rw [haddr] at h3
      exact h3
    rw [h1, h2]
  have hE : limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
          (2112 + 32 * (p - k))).toNat) (p + 1) * Limbs.radix +
        (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) 0).toNat =
      limbSum (fun k => (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) k).toNat)
        (p + 2) := by
    rw [limbSum_congr (p + 1) hstF]
    exact limbSum_shift
      (fun k => (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) k).toNat) (p + 1)
  have hmm := limbSum_fastRepresents hm
  simp only [Nat.zero_add] at hmm
  have hsmF : ∀ k, k < p + 1 →
      (MachineState.readWord (rowMid mem pa pb (p + 2) i) (32 * (p - k))).toNat =
      (MachineState.readWord mem (32 * (p + 2 - 1 - (k + 1)))).toNat := by
    intro k hk
    have h1 : MachineState.readWord (rowMid mem pa pb (p + 2) i) (32 * (p - k)) =
        MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory (32 * (p - k)) := by
      rw [rowMid_def]
      exact readWord_midMem_low' _ _ _ (by omega)
    have h2 : MachineState.readWord (rowL1 mem pa pb (p + 2) i).memory
        (32 * (p - k)) = MachineState.readWord mem (32 * (p - k)) :=
      readWord_l1Step_low mem (rowBi mem pb (p + 2) i) pa (p + 2) (32 * (p - k))
        (p + 2) (by omega)
    have haddr : 32 * (p + 2 - 1 - (k + 1)) = 32 * (p - k) := by omega
    rw [h1, h2, haddr]
  have hF : limbSum (fun k => (MachineState.readWord (rowMid mem pa pb (p + 2) i)
          (32 * (p - k))).toNat) (p + 1) * Limbs.radix +
        (MachineState.readWord mem (32 * (p + 2) - 32)).toNat = mm := by
    rw [limbSum_congr (p + 1) hsmF]
    have h0 : 32 * (p + 2) - 32 = 32 * (p + 2 - 1 - 0) := by omega
    rw [h0]
    rw [limbSum_shift (fun k =>
      (MachineState.readWord mem (32 * (p + 2 - 1 - k))).toNat) (p + 1)]
    exact hmm
  have hG : limbSum (fun k => (l1Val mem (rowBi mem pb (p + 2) i) pa (p + 2) k).toNat)
        (p + 2) +
      (rowL1 mem pa pb (p + 2) i).carry.toNat *
        (Limbs.radix ^ (p + 1) * Limbs.radix) =
      tlow + (rowBi mem pb (p + 2) i).toNat * a := by
    rw [← hpow]
    exact l1_row mem (rowBi mem pb (p + 2) i) pa (p + 2) tlow a hn32 hpaFit ha ht
  rw [lowValue_rowMem mem pa pb p i hn32, hFtn, hFts, hpow]
  exact row_alg hA hB hC hD hE hF hG

private theorem div_of_mul {x y r : Nat} (hr : 0 < r) (h : x * r = y) : y / r = x := by
  have hy : y / r = x * r / r := by rw [h]
  rw [hy, Nat.mul_div_assoc x (dvd_refl r), Nat.div_self hr, Nat.mul_one]

theorem rows_invariant (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 8)
    (hpaFit : pa + 32 * (p + 2) ≤ 2048 ∨ 2368 ≤ pa) (hpbFit : pb + 32 * (p + 2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    ∀ i, i ≤ p + 2 → ∃ Q,
      tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) *
          Limbs.radix ^ i = a * (b % Limbs.radix ^ i) + Q * mm ∧
        tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) (p + 2) < 2 * mm := by
  intro i
  induction i with
  | zero =>
      intro _
      have hlow0 : Csub.lowValue (mpZeroed s mem (p + 2)) 2112 (p + 2) (p + 2) = 0 :=
        Model.fastRepresents_value_unique
          (Csub.fastRepresents_lowValue (mpZeroed s mem (p + 2)) 2112 (p + 2))
          (fastRepresents_mpZeroed s mem (p + 2))
      have hzero : tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) 0)
          (p + 2) = 0 := by
        show tValue (mpZeroed s mem (p + 2)) (p + 2) = 0
        simp only [tValue, hlow0, readWord_mpZeroed_tn,
          Challenge.EvmProof.Word.word_toNat_ofNat]
        simp
      exact ⟨0, by rw [hzero, pow_zero, Nat.mod_one]; simp, by rw [hzero]; omega⟩
  | succ i ih =>
      intro hi
      obtain ⟨Q, hinv, hlt⟩ := ih (by omega)
      simp only [tValue] at hinv hlt ⊢
      simp only [rowsMem]
      have hpaR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa (p + 2) a :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i pa (p + 2) a hn32
          hpaFit ha
      have hpbR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pb (p + 2) b :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i pb (p + 2) b hn32
          (Or.inl hpbFit) hb
      have hmR : Model.FastRepresents
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 0 (p + 2) mm :=
        fastRepresents_monpro_preserved s mem pa pb (p + 2) i 0 (p + 2) mm hn32
          (by omega) hm
      have hminvR : ((MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
            (32 * (p + 2) - 32)).toNat *
          (MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2720).toNat + 1) %
          2 ^ 256 = 0 := by
        rw [readWord_monpro_preserved s mem pa pb (p + 2) i (32 * (p + 2) - 32) hn32
            (Or.inl (by omega)),
          readWord_monpro_preserved s mem pa pb (p + 2) i 2720 hn32 (Or.inr (by omega))]
        exact hminv
      have hrow := row_equation (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb p i a mm
        (Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112
          (p + 2) (p + 2))
        hn32 hpaFit hpaR hmR
        (Csub.fastRepresents_lowValue
          (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112 (p + 2)) hminvR
      have hbi : (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat = b / Limbs.radix ^ i % Limbs.radix := by
        simp only [rowBi]
        exact Model.readLimb_of_fastRepresents hpbR (by omega)
      have hdiv : Limbs.radix ∣
          (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              2080).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112
              (p + 2) (p + 2) +
            a * (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pb (p + 2) i).toNat +
            (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i).memory (p + 2)).toNat * mm := by
        refine ⟨(MachineState.readWord (rowMem
              (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) pa pb (p + 2) i)
              2080).toNat * Limbs.radix ^ (p + 2) +
            Csub.lowValue (rowMem (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
              pa pb (p + 2) i) 2112 (p + 2) (p + 2), ?_⟩
        rw [← hrow]
        ring
      have hquot := div_of_mul Limbs.radix_pos hrow
      obtain ⟨hstep1, hstep2⟩ := Model.cios_step (β := Limbs.radix) (m := mm) (a := a)
        (bpre := b % Limbs.radix ^ i)
        (bi := (rowBi (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pb (p + 2) i).toNat)
        (t := (MachineState.readWord
            (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2080).toNat *
            Limbs.radix ^ (p + 2) +
          Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i) 2112
            (p + 2) (p + 2))
        (Q := Q)
        (mu := (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
          pa pb (p + 2) i).memory (p + 2)).toNat) (i := i)
        Limbs.radix_pos ham (word_lt_size _) hlt (word_lt_size _) hinv hdiv
      refine ⟨Q + (rowMu (rowL1 (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) i)
        pa pb (p + 2) i).memory (p + 2)).toNat * Limbs.radix ^ i, ?_, ?_⟩
      · rw [← hquot, hstep1, mod_pow_succ, hbi]
      · rw [← hquot]
        exact hstep2

theorem monpro_tn_le_one (s : State) (mem : ByteArray) (pa pb p : Nat) (a b mm : Nat)
    (hn32 : p + 2 ≤ 8)
    (hpaFit : pa + 32 * (p + 2) ≤ 2048 ∨ 2368 ≤ pa) (hpbFit : pb + 32 * (p + 2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
      2080).toNat ≤ 1 := by
  obtain ⟨-, -, hlt⟩ := rows_invariant s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm
    ham hmpos hminv (p + 2) (Nat.le_refl _)
  simp only [tValue] at hlt
  have hmlt : mm < Limbs.radix ^ (p + 2) := hm.1
  have hlow : Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
      2112 (p + 2) (p + 2) < Limbs.radix ^ (p + 2) := Csub.lowValue_lt _ _ _ _
  by_contra hcon
  have hge : 2 ≤ (MachineState.readWord
      (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 2080).toNat := by omega
  have hmul : 2 * Limbs.radix ^ (p + 2) ≤
      (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
        2080).toNat * Limbs.radix ^ (p + 2) := Nat.mul_le_mul_right _ hge
  omega

theorem monpro_represents (s : State) (mem : ByteArray) (pa pb p pdst : Nat)
    (a b mm : Nat) (hn32 : p + 2 ≤ 8)
    (hpaFit : pa + 32 * (p + 2) ≤ 2048 ∨ 2368 ≤ pa) (hpbFit : pb + 32 * (p + 2) ≤ 2048)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (hodd : mm % 2 = 1) (ham : a < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0) :
    Model.FastRepresents
      (Csub.csResultMemory
        (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) pdst)
      pdst (p + 2) (Model.montMul mm (Limbs.radix ^ (p + 2)) a b) := by
  have hmpos : 0 < mm := by omega
  obtain ⟨Q, hinv, hlt⟩ := rows_invariant s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb
    hm ham hmpos hminv (p + 2) (Nat.le_refl _)
  have htn1 := monpro_tn_le_one s mem pa pb p a b mm hn32 hpaFit hpbFit ha hb hm ham
    hmpos hminv
  have hbmod : b % Limbs.radix ^ (p + 2) = b := Nat.mod_eq_of_lt hb.1
  rw [hbmod] at hinv
  have hcop : Nat.Coprime (Limbs.radix ^ (p + 2)) mm :=
    Model.coprime_radix_pow_of_odd hodd (p + 2)
  have hval : Model.montMul mm (Limbs.radix ^ (p + 2)) a b =
      tValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) (p + 2) % mm :=
    Model.montMul_eq_mod_of_mul_eq hmpos hcop hinv
  have hmR : Model.FastRepresents
      (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 0 (p + 2) mm :=
    fastRepresents_monpro_preserved s mem pa pb (p + 2) (p + 2) 0 (p + 2) mm hn32
      (by omega) hm
  rw [hval]
  simp only [tValue] at hlt ⊢
  exact Csub.csub_correct (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
    (p + 2)
    (Csub.lowValue (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 2112
      (p + 2) (p + 2))
    mm
    (MachineState.readWord (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2))
      2080).toNat
    pdst (by omega) hn32
    (Csub.fastRepresents_lowValue
      (rowsMem (mpZeroed s mem (p + 2)) pa pb (p + 2) (p + 2)) 2112 (p + 2))
    hmR rfl htn1 hmpos hlt

#print axioms monpro_represents
end Challenge.Modexp.Submission.Proofs.Fast.StagedMonpro
