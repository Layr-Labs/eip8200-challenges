import Challenge.Modexp.Submission.Proofs.R5.LoopMeaning
import Challenge.Modexp.Submission.Proofs.R5.ProductMeaning
import Challenge.Modexp.Submission.Proofs.R5.TailMeaning
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000
set_option exponentiation.threshold 4096

/-!
# The r5 route from the loop head (4037) to RETURN

Over abstract digits: `k` squares (`LoopRun.loop`, `LoopMeaning.step`), the product with the
base digits in memory (`TailRun.product`, `ProductMeaning.pr_exact`), at most two
normalization rounds and the pack. The result is `(w^(2^k) * B).val` in `ZMod N` when the
start digits have value `≡ w * R`.
-/

namespace CycleSubmission.R5.Route
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open HistoricalSearch.MixedMontgomery
open CycleSubmission.WordArithmetic
open CycleSubmission.R5.LoopRun CycleSubmission.R5.LoopMeaning
open CycleSubmission.R5.ProductRun CycleSubmission.R5.ProductMeaning
open CycleSubmission.R5.ExecNorm CycleSubmission.R5.TailRun

/-! ## Digit arithmetic -/

theorem val_eq (x : D5) : val x = x.d0.toNat + x.d1.toNat * 2^240 + x.d2.toNat * 2^480 +
    x.d3.toNat * 2^720 + x.d4.toNat * 2^960 := by
  simp only [val, radix]; norm_num

theorem low4 (a : D5) (h0 : a.d0.toNat < radix) (h1 : a.d1.toNat < radix) (h2 : a.d2.toNat < radix)
    (h3 : a.d3.toNat < radix) :
    a.d0.toNat + a.d1.toNat * radix + a.d2.toNat * radix^2 + a.d3.toNat * radix^3 < radix^4 := by
  have s1 : (a.d1.toNat + 1) * radix ≤ radix * radix := Nat.mul_le_mul_right _ h1
  have s2 : (a.d2.toNat + 1) * radix^2 ≤ radix * radix^2 := Nat.mul_le_mul_right _ h2
  have s3 : (a.d3.toNat + 1) * radix^3 ≤ radix * radix^3 := Nat.mul_le_mul_right _ h3
  linarith

theorem lt_of_top (a n : D5) (h0 : a.d0.toNat < radix) (h1 : a.d1.toNat < radix)
    (h2 : a.d2.toNat < radix) (h3 : a.d3.toNat < radix) (h : a.d4.toNat < n.d4.toNat) :
    val a < val n := by
  have hl := low4 a h0 h1 h2 h3
  have s4 : (a.d4.toNat + 1) * radix^4 ≤ n.d4.toNat * radix^4 := Nat.mul_le_mul_right _ h
  have z0 := Nat.zero_le n.d0.toNat
  have z1 := Nat.zero_le (n.d1.toNat * radix)
  have z2 := Nat.zero_le (n.d2.toNat * radix^2)
  have z3 := Nat.zero_le (n.d3.toNat * radix^3)
  unfold val
  linarith

/-- A value below `2^1025` has its top digit below `2^65`. -/
theorem top65 (a : D5) (V : Nat) (hv : val a < 2 * V) (hV : V < 2^1024) : a.d4.toNat < 2^65 := by
  have ht : a.d4.toNat * radix^4 ≤ val a := by unfold val; omega
  have hr : radix^4 = 2^960 := by norm_num [radix]
  rw [hr] at ht
  have h2 : a.d4.toNat * 2^960 < 2^65 * 2^960 :=
    calc a.d4.toNat * 2^960 ≤ val a := ht
      _ < 2 * V := hv
      _ < 2 * 2^1024 := by omega
      _ = 2^65 * 2^960 := by norm_num
  exact Nat.lt_of_mul_lt_mul_right h2

def prOut (x : D5) (n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M : UInt256) : D5 :=
  ⟨prV5_5 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M,
   prV6_6 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M,
   prV7_7 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M,
   prV8_8 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M,
   prV8_0 x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 M⟩

/-! ## Squares and the product -/

section
variable (n0 n1 n2 n3 n4 P inv ninv : UInt256) (N : Nat)
  (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
  (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
  (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0)
  (hNval : N = val ⟨n0, n1, n2, n3, n4⟩) (hodd : N % 2 = 1) (h4 : 4*N ≤ RouteMath.R)
include hinv hP hn1 hn2 hn3 hn4 hn0 hN hNval hodd h4

theorem iter_spec (m : Nat) : ∀ (x : D5) (c : UInt256) (w : ZMod N), ok x →
    val x + 2*N ≤ RouteMath.R → ((val x : Nat) : ZMod N) = w * RouteMath.R →
    ok (iter n1 n2 n3 n4 P inv n0 m x c).1 ∧ val (iter n1 n2 n3 n4 P inv n0 m x c).1 + 2*N ≤ RouteMath.R ∧
    ((val (iter n1 n2 n3 n4 P inv n0 m x c).1 : Nat) : ZMod N) = w^(2^m) * RouteMath.R := by
  induction m with
  | zero =>
    intro x c w hx hb hw
    refine ⟨hx, hb, ?_⟩
    simpa [iter] using hw
  | succ m ih =>
    intro x c w hx hb hw
    have hNpos : 0 < N := by omega
    obtain ⟨hok, hb', Q, hQ, hex⟩ := step n0 n1 n2 n3 n4 P inv ninv N hinv hP hn1 hn2 hn3 hn4 hn0 hN
      hNval x c hx h4 hNpos hb
    have hz := RouteMath.square_zmod hodd w _ _ Q hw hex
    obtain ⟨r1, r2, r3⟩ := ih (next n1 n2 n3 n4 P inv n0 x c) (dec n1 n2 n3 n4 P inv n0 x c) (w^2) hok hb' hz
    refine ⟨r1, r2, ?_⟩
    show ((val (iter n1 n2 n3 n4 P inv n0 m (next n1 n2 n3 n4 P inv n0 x c)
      (dec n1 n2 n3 n4 P inv n0 x c)).1 : Nat) : ZMod N) = _
    rw [r3, ← pow_mul, show 2 * 2^m = 2^(m+1) by ring]

omit h4 in
theorem product_spec (x : D5) (cntp b0 b1 b2 b3 b4 : UInt256) (B : Nat) (w : ZMod N)
    (hx : ok x) (hw : ((val x : Nat) : ZMod N) = w * RouteMath.R)
    (hb : ok ⟨b0, b1, b2, b3, b4⟩) (hB : val ⟨b0, b1, b2, b3, b4⟩ = B) (hBN : B < N) :
    (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M).d0.toNat < radix ∧
    (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M).d1.toNat < radix ∧
    (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M).d2.toNat < radix ∧
    (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M).d3.toNat < radix ∧
    val (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M) < 2*N ∧
    ((val (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M) : Nat) : ZMod N) = w * B := by
  have hxv := val_lt x hx
  obtain ⟨hx0, hx1, hx2, hx3, hx4⟩ := hx
  obtain ⟨hb0, hb1, hb2, hb3, hb4⟩ := hb
  obtain ⟨hq, hz, heq⟩ := pr_exact x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0
    Digits.M ninv N hinv hP hx0 hx1 hx2 hx3 hx4 hn1 hn2 hn3 hn4 hb0 hb1 hb2 hb3 hb4 hn0 hN rfl
  simp only [weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, pow_zero,
    pow_one, mul_one, prDd, prXd, prYd, prNd] at heq
  have hQ : weighted radix 5 (prQd x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0
      Digits.M) < RouteMath.R := by
    simp only [weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add, pow_zero,
      pow_one, mul_one]
    exact bound5 _ _ _ _ _ (hq 0 (by decide)) (hq 1 (by decide)) (hq 2 (by decide))
      (hq 3 (by decide)) (hq 4 (by decide))
  have hexact : val (prOut x n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4 n0 Digits.M) * RouteMath.R =
      val x * B + weighted radix 5 (prQd x.d0 x.d1 x.d2 x.d3 x.d4 n1 n2 n3 n4 P inv cntp b0 b1 b2 b3 b4
        n0 Digits.M) * N := by
    rw [← radix_pow5, hNval, ← hB]
    simp only [val, prOut, weighted, Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add,
      pow_zero, pow_one, mul_one]
    linarith [heq]
  have hNpos : 0 < N := by omega
  have hT := RouteMath.product_bound N RouteMath.R (val x) B _ _ (by norm_num [RouteMath.R]) hNpos
    hxv hBN hQ hexact
  have hzm := RouteMath.product_zmod hodd w (val x) B _ _ hw hexact
  have l0 := hz 0 (by decide); have l1 := hz 1 (by decide)
  have l2 := hz 2 (by decide); have l3 := hz 3 (by decide)
  simp only [prDd] at l0 l1 l2 l3
  exact ⟨l0, l1, l2, l3, hT, hzm⟩
end

/-! ## Normalization -/

section
variable (s : State) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
  (n0 n1 n2 n3 n4 P inv cntp : UInt256) (rest : List UInt256) (N : Nat)
  (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat)
  (h_n0 : MachineState.readWord s.memory 160 = n0) (h_M : MachineState.readWord s.memory 224 = Digits.M)
  (hn0 : n0.toNat < radix) (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix)
  (hn4 : n4.toNat < 2^65) (hNval : N = val ⟨n0, n1, n2, n3, n4⟩)
include env hcap hact h_n0 h_M hn0 hn1 hn2 hn3 hn4 hNval

/-- The value below `N`: one round ends at `r5_done` with the digits unchanged. -/
theorem finish_lt (a : D5) (h0 : a.d0.toNat < radix) (h1 : a.d1.toNat < radix)
    (h2 : a.d2.toNat < radix) (h3 : a.d3.toNat < radix) (h4 : a.d4.toNat < 2^65) (hT : val a < N) :
    Nonempty (GasSteps (normAt s n1 n2 n3 n4 P inv cntp rest 5184 a.d0 a.d1 a.d2 a.d3 a.d4)
      (normAt s n1 n2 n3 n4 P inv cntp rest 5285 a.d0 a.d1 a.d2 a.d3 a.d4)) := by
  by_cases hlt : (UInt256.lt a.d4 n4).toNat = 0
  · have hc := NormMath.chain a.d0 a.d1 a.d2 a.d3 a.d4 n0 n1 n2 n3 n4 _ _ _ _ _ rfl rfl rfl rfl rfl
      h0 h1 h2 h3 h4 hn0 hn1 hn2 hn3 hn4
    have hNv : n0.toNat + n1.toNat * 2^240 + n2.toNat * 2^480 + n3.toNat * 2^720 + n4.toNat * 2^960 = N := by
      rw [hNval, val_eq]
    rw [hNv, ← val_eq, if_neg (by omega)] at hc
    have hneg : (blk5192_o0 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M).toNat = 1 := hc.1
    exact ⟨((roundSub s env a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M rest hcap hact
      h_n0 h_M hlt).cast rfl (by rw [hneg]; rfl)).trans
      (keep s env a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp rest hcap hact _ _ _ _ _)⟩
  · exact ⟨roundLt s env a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp rest hcap hact hlt⟩

/-- A value below `2N` normalizes to its residue in at most two rounds. -/
theorem norm_spec (a : D5) (h0 : a.d0.toNat < radix) (h1 : a.d1.toNat < radix)
    (h2 : a.d2.toNat < radix) (h3 : a.d3.toNat < radix) (h4 : a.d4.toNat < 2^65) (hT : val a < 2*N) :
    ∃ e : D5, e.d0.toNat < radix ∧ e.d1.toNat < radix ∧ e.d2.toNat < radix ∧ e.d3.toNat < radix ∧
      e.d4.toNat < 2^65 ∧ val e = val a % N ∧
      Nonempty (GasSteps (normAt s n1 n2 n3 n4 P inv cntp rest 5184 a.d0 a.d1 a.d2 a.d3 a.d4)
        (normAt s n1 n2 n3 n4 P inv cntp rest 5285 e.d0 e.d1 e.d2 e.d3 e.d4)) := by
  by_cases hlt : val a < N
  · exact ⟨a, h0, h1, h2, h3, h4, (Nat.mod_eq_of_lt hlt).symm,
      finish_lt s env n0 n1 n2 n3 n4 P inv cntp rest N hcap hact h_n0 h_M hn0 hn1 hn2 hn3 hn4 hNval
        a h0 h1 h2 h3 h4 hlt⟩
  · have hge : N ≤ val a := by omega
    have hlt4 : (UInt256.lt a.d4 n4).toNat = 0 := by
      rw [Challenge.EvmProof.Word.word_toNat_lt]
      split_ifs with h
      · exact absurd (lt_of_top a ⟨n0, n1, n2, n3, n4⟩ h0 h1 h2 h3 h) (by rw [← hNval]; omega)
      · rfl
    have hc := NormMath.chain a.d0 a.d1 a.d2 a.d3 a.d4 n0 n1 n2 n3 n4 _ _ _ _ _ rfl rfl rfl rfl rfl
      h0 h1 h2 h3 h4 hn0 hn1 hn2 hn3 hn4
    have hNv : n0.toNat + n1.toNat * 2^240 + n2.toNat * 2^480 + n3.toNat * 2^720 + n4.toNat * 2^960 = N := by
      rw [hNval, val_eq]
    rw [hNv, ← val_eq, if_pos hge] at hc
    obtain ⟨hneg, hsub⟩ := hc
    obtain ⟨hdv, d0b, d1b, d2b, d3b, d4b⟩ := hsub hge
    have hneg' : (blk5192_o0 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M).toNat = 0 := hneg
    let d : D5 := ⟨blk5192_o5 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M,
      blk5192_o4 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M,
      blk5192_o3 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M,
      blk5192_o2 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M,
      blk5192_o1 a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp n0 Digits.M⟩
    have hd : val d = val a - N := by rw [val_eq]; exact hdv
    have hdN : val d < N := by omega
    obtain ⟨g2⟩ := finish_lt s env n0 n1 n2 n3 n4 P inv cntp rest N hcap hact h_n0 h_M hn0 hn1 hn2 hn3 hn4
      hNval d d0b d1b d2b d3b d4b hdN
    refine ⟨d, d0b, d1b, d2b, d3b, d4b, ?_, ⟨((roundSub s env a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv
      cntp n0 Digits.M rest hcap hact h_n0 h_M hlt4).cast rfl (by rw [hneg']; rfl)).trans
      ((replace s env a.d0 a.d1 a.d2 a.d3 a.d4 n1 n2 n3 n4 P inv cntp rest hcap hact _ _ _ _ _).trans g2)⟩⟩
    rw [hd, Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
end

/-! ## From the loop head to RETURN -/

theorem from_head (s : State) (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (rest : List UInt256) (hcap : rest.length ≤ 960)
    (x : D5) (n0 n1 n2 n3 n4 P inv ninv b0 b1 b2 b3 b4 c : UInt256) (N B k : Nat) (w : ZMod N)
    (hinv : inv = UInt256.shiftLeft ninv (UInt256.ofNat 16)) (hP : P = CycleSubmission.WordArithmetic.P)
    (hn1 : n1.toNat < radix) (hn2 : n2.toNat < radix) (hn3 : n3.toNat < radix) (hn4 : n4.toNat < radix)
    (hn0 : n0.toNat = N % radix) (hN : (N*ninv.toNat+1) % 2^256 = 0)
    (hNval : N = val ⟨n0, n1, n2, n3, n4⟩) (hodd : N % 2 = 1) (hNlt : N < 2^1024)
    (h_b0 : MachineState.readWord s.memory 0 = b0) (h_b1 : MachineState.readWord s.memory 32 = b1)
    (h_b2 : MachineState.readWord s.memory 64 = b2) (h_b3 : MachineState.readWord s.memory 96 = b3)
    (h_b4 : MachineState.readWord s.memory 128 = b4) (h_n0 : MachineState.readWord s.memory 160 = n0)
    (h_inv : MachineState.readWord s.memory 192 = inv) (h_M : MachineState.readWord s.memory 224 = Digits.M)
    (hb : ok ⟨b0, b1, b2, b3, b4⟩) (hB : val ⟨b0, b1, b2, b3, b4⟩ = B) (hBN : B < N)
    (hk : 1 ≤ k) (hc : c.toNat = k - 1)
    (hx : ok x) (hxb : val x + 2*N ≤ RouteMath.R) (hw : ((val x : Nat) : ZMod N) = w * RouteMath.R) :
    ∃ t : State, Nonempty (GasSteps (head s x n1 n2 n3 n4 P inv c rest) t) ∧ t.halt = .Returned ∧
      t.hReturn = Precompile.natToBytes ((w^(2^k) * (B : ZMod N)).val) 128 ∧
      t.callStack = s.callStack := by
  have hpow : (2:Nat)^1024 * 4 ≤ 2^1200 := by norm_num
  have h4 : 4*N ≤ RouteMath.R := by unfold RouteMath.R; omega
  have hn4' : n4.toNat < 2^65 := top65 ⟨n0, n1, n2, n3, n4⟩ N (by rw [← hNval]; omega) hNlt
  have hn0' : n0.toNat < radix := by rw [hn0]; exact Nat.mod_lt _ (by norm_num [radix])
  have gl := loop s n1 n2 n3 n4 P inv n0 rest env hcap hact h_n0 h_inv (k-1) x c hc
  obtain ⟨hXok, hXb, hXw⟩ := iter_spec n0 n1 n2 n3 n4 P inv ninv N hinv hP hn1 hn2 hn3 hn4 hn0 hN hNval
    hodd h4 (k-1+1) x c w hx hxb hw
  set X := (iter n1 n2 n3 n4 P inv n0 (k - 1 + 1) x c).1 with hX
  set C := (iter n1 n2 n3 n4 P inv n0 (k - 1 + 1) x c).2 with hC
  have gp := product s env X.d0 X.d1 X.d2 X.d3 X.d4 n1 n2 n3 n4 P inv C b0 b1 b2 b3 b4 n0 Digits.M rest
    hcap hact h_b0 h_b1 h_b2 h_b3 h_b4 h_n0 h_inv h_M
  obtain ⟨t0, t1, t2, t3, hT, hTw⟩ := product_spec n0 n1 n2 n3 n4 P inv ninv N hinv hP hn1 hn2 hn3 hn4
    hn0 hN hNval hodd X C b0 b1 b2 b3 b4 B (w^(2^(k-1+1))) hXok hXw hb hB hBN
  set T := prOut X n1 n2 n3 n4 P inv C b0 b1 b2 b3 b4 n0 Digits.M with hTdef
  have t4 := top65 T N hT hNlt
  obtain ⟨e, e0, e1, e2, e3, e4, hev, ⟨gn⟩⟩ := norm_spec s env n0 n1 n2 n3 n4 P inv C rest N hcap hact
    h_n0 h_M hn0' hn1 hn2 hn3 hn4' hNval T t0 t1 t2 t3 t4 hT
  have gf := finish s env e.d0 e.d1 e.d2 e.d3 e.d4 n1 n2 n3 n4 P inv C rest hcap hact
  have hv5 : TailMeaning.val5 e.d0 e.d1 e.d2 e.d3 e.d4 = val e := by rw [val_eq]; rfl
  have hk' : k - 1 + 1 = k := by omega
  have he4 : e.d4.toNat < 2^240 := lt_trans e4 (by norm_num)
  refine ⟨_, ⟨gl.trans (gp.trans (gn.trans gf))⟩, rfl, ?_, rfl⟩
  rw [TailMeaning.returned s _ e.d0 e.d1 e.d2 e.d3 e.d4 n1 n2 n3 n4 P inv C e0 e1 e2 e3 he4
    (by rw [hv5, hev]; exact lt_trans (Nat.mod_lt _ (by omega)) hNlt)]
  rw [hv5, hev, ← ZMod.val_natCast, hTw, hk']

end CycleSubmission.R5.Route
