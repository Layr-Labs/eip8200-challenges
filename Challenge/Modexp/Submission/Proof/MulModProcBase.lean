import Challenge.Modexp.Submission.AsmLib
import Challenge.Modexp.Submission.Proof.YulLimbs
import Challenge.Modexp.Submission.Program

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Base machinery for the `mulModBig` PROCEDURE proof

Value-level arithmetic, memory-frame predicates, machine-level step
helpers, and the loop lemmas (scan / top-bit / copy-in / zero / tail) for
the procedure-based program's `mulModProc` section.  Ported from the
verified inline-fragment development (`proof-hold/MulModBase.lean`,
`proof-hold/AddModProof.lean`) with the procedure changes: the multiplier
region is addressed through the `BPTR` cell (set by the call site), the
bit loop calls the `addMod` PROCEDURE instead of inlined fragments, and
the section ends with the trailing `.dynJump` return.

The bits loop itself (which consumes the `addMod` procedure through the
`AddModProcSpec` contract) lives in `MulModProcProof.lean`.
-/

namespace Challenge.Modexp.Submission.Proof.MulModProc

open Challenge.Modexp.Submission
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proof.YulLimbs
open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState loadWord storeWord b2w)

/-! ## Word-level arithmetic helpers -/

/-- The wrapped difference of two words, on `Nat`. -/
theorem toNat_sub_eq (a b : U256) :
    (a - b).toNat = (a.toNat + 2 ^ 256 - b.toNat) % 2 ^ 256 := by
  rw [BitVec.toNat_sub]
  congr 1
  omega

/-- The bitwise or of two words, on `Nat`. -/
theorem toNat_or_eq (a b : U256) : (a ||| b).toNat = (a.toNat ||| b.toNat) := by
  exact BitVec.toNat_or a b

/-- The word value of a `b2w`. -/
theorem toNat_b2w_eq (b : Bool) : (b2w b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- The two-word or of carry bits, on `Nat`. -/
theorem toNat_lor_b2w (b₁ b₂ : Bool) :
    ((b2w b₁) ||| (b2w b₂)).toNat = ((if b₁ then 1 else 0) ||| (if b₂ then 1 else 0)) := by
  rw [toNat_or_eq, toNat_b2w_eq, toNat_b2w_eq]

/-- A word is determined by its value. -/
theorem word_of_toNat {v : U256} {k : Nat} (h : v.toNat = k) (hk : k < 2 ^ 256) :
    v = BitVec.ofNat 256 k := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, h]

/-- `ofNat` multiplication. -/
theorem ofNat_mul256 (a b : Nat) :
    BitVec.ofNat 256 a * BitVec.ofNat 256 b = BitVec.ofNat 256 (a * b) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.mul_mod]

/-- `ofNat` addition. -/
theorem ofNat_add256 (a b : Nat) :
    BitVec.ofNat 256 a + BitVec.ofNat 256 b = BitVec.ofNat 256 (a + b) := by
  apply BitVec.eq_of_toNat_eq
  simp [Nat.add_mod]

/-- A nonzero `ofNat`. -/
theorem ofNat_ne_zero {k : Nat} (hk : k < 2 ^ 256) (hne : k ≠ 0) :
    BitVec.ofNat 256 k ≠ 0 := by
  intro h
  apply hne
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk] at this

/-! ## Cell and pinning helpers -/

/-- The cells used by the procedures (all 32-aligned, all at or above
`Ncell`, all at or below `TOP`).  Extends the inline fragment list with
the procedure call-setup cells `BPTR`, `ADST`, `ASRC`. -/
def fragCells : List Nat :=
  [Ncell, Icell, Jcell, Wcell, C1, C2, HIcell, BPTR, T0, T1, T2, ADST, ASRC,
    I2, AOFF, AX, AY, AS, AZ]

theorem fragCells_aligned : ∀ c ∈ fragCells, c % 32 = 0 := by decide

theorem fragCells_ge : ∀ c ∈ fragCells, Ncell ≤ c := by decide

theorem fragCells_le : ∀ c ∈ fragCells, c ≤ TOP := by decide

/-- Distinct fragment cells sit in disjoint 32-byte windows. -/
theorem cells_disj {c d : Nat} (hc : c ∈ fragCells) (hd : d ∈ fragCells) (hne : c ≠ d) :
    c + 32 ≤ d ∨ d + 32 ≤ c := by
  have h1 := fragCells_aligned c hc
  have h2 := fragCells_aligned d hd
  omega

/-- The top cell address is below `2 ^ 256`. -/
theorem TOP_lt : (TOP : Nat) < 2 ^ 256 := by decide

/-- The `BPTR` cell address is below `2 ^ 256`. -/
theorem BPTR_lt : (BPTR : Nat) < 2 ^ 256 := by decide

/-- Every fragment cell is pinned inside the active window. -/
theorem cell_pinned {yst : EvmState} (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    {c : Nat} (hc : c ∈ fragCells) : c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat := by
  have hmem : c ≤ TOP := fragCells_le c hc
  refine ⟨Nat.lt_of_le_of_lt hmem TOP_lt, ?_⟩
  have hTOP : (TOP : Nat) = 0x1f20 := rfl
  omega

/-- `exprOK` for a cell load. -/
theorem exprOK_load_cell {yst : EvmState} (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    {c : Nat} (hc : c ∈ fragCells) : exprOK (.load c) yst := cell_pinned haw hc

theorem Ncell_lt_pow : (Ncell : Nat) < 2 ^ 256 := by decide

/-! ## Statement-level helpers with computed values -/

/-- `store c e` with the value already computed: the effect is exactly the word
write. -/
theorem store_cell_val [model : ExternalModel] {prog : List Asm} {c : Nat} {e : Expr}
    {w : U256} {k : List Asm} {σ : List AVal} {yst : EvmState}
    (hev : evalExpr e yst = w) (he : exprOK e yst)
    (hc : c < 2 ^ 256 ∧ c + 32 ≤ 32 * yst.activeWords.toNat) :
    ASteps prog ⟨store c e ++ k, σ, yst⟩
      ⟨k, σ, { yst with memory := (storeWord yst.memory c w) }⟩ := by
  have h := store_steps (model := model) (prog := prog) (c := c) (e := e)
    (k := k) (σ := σ) he hc
  rwa [hev] at h

/-- `storeAt addrE valE` with address and value already computed. -/
theorem storeAt_val [model : ExternalModel] {prog : List Asm}
    {addrE valE : Expr} {addr : Nat} {w : U256} {k : List Asm} {σ : List AVal}
    {yst : EvmState}
    (haddr : evalExpr addrE yst = BitVec.ofNat 256 addr)
    (hval : evalExpr valE yst = w)
    (haddrLt : addr < 2 ^ 256)
    (hv : exprOK valE yst) (ha : exprOK addrE yst)
    (hpin : addr + 32 ≤ 32 * yst.activeWords.toNat) :
    ASteps prog ⟨storeAt addrE valE ++ k, σ, yst⟩
      ⟨k, σ, { yst with memory := (storeWord yst.memory addr w) }⟩ := by
  have h := storeAt_steps (model := model) (prog := prog) (k := k) (σ := σ) hv ha
    (by rw [haddr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddrLt]; exact hpin)
  rw [haddr, hval, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddrLt] at h
  exact h

/-- A word-level `ult` on `ofNat` literals. -/
theorem ult_ofNat_eq {a b : Nat} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) :
    (BitVec.ofNat 256 a).ult (BitVec.ofNat 256 b) = decide (a < b) := by
  show decide ((BitVec.ofNat 256 a).toNat < (BitVec.ofNat 256 b).toNat) = decide (a < b)
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]

/-- `jumpUnlessLt e₁ e₂ l`, fall-through with the values computed. -/
theorem jumpUnlessLt_val_fall [model : ExternalModel] {prog : List Asm}
    {e₁ e₂ : Expr} {l : Label} {v₁ v₂ : Nat} {k : List Asm} {σ : List AVal}
    {yst : EvmState}
    (h₁ : evalExpr e₁ yst = BitVec.ofNat 256 v₁) (h₂ : evalExpr e₂ yst = BitVec.ofNat 256 v₂)
    (hv₁ : exprOK e₁ yst) (hv₂ : exprOK e₂ yst)
    (hv₁lt : v₁ < 2 ^ 256) (hv₂lt : v₂ < 2 ^ 256)
    (hlt : v₁ < v₂) :
    ASteps prog ⟨jumpUnlessLt e₁ e₂ l ++ k, σ, yst⟩ ⟨k, σ, yst⟩ := by
  refine jumpUnlessLt_fall hv₁ hv₂ ?_
  rw [h₁, h₂, ult_ofNat_eq hv₁lt hv₂lt]
  simp only [decide_eq_true_eq]
  exact hlt

/-- `jumpUnlessLt e₁ e₂ l`, taken with the values computed. -/
theorem jumpUnlessLt_val_taken [model : ExternalModel] {prog : List Asm}
    {e₁ e₂ : Expr} {l : Label} {v₁ v₂ : Nat} {c' : List Asm} {k : List Asm}
    {σ : List AVal} {yst : EvmState}
    (h₁ : evalExpr e₁ yst = BitVec.ofNat 256 v₁) (h₂ : evalExpr e₂ yst = BitVec.ofNat 256 v₂)
    (hv₁ : exprOK e₁ yst) (hv₂ : exprOK e₂ yst)
    (hv₁lt : v₁ < 2 ^ 256) (hv₂lt : v₂ < 2 ^ 256)
    (hlt : v₂ ≤ v₁)
    (hfind : findLabel l prog = some c') :
    ASteps prog ⟨jumpUnlessLt e₁ e₂ l ++ k, σ, yst⟩ ⟨c', σ, yst⟩ := by
  refine jumpUnlessLt_taken hv₁ hv₂ ?_ hfind
  rw [h₁, h₂, ult_ofNat_eq hv₁lt hv₂lt]
  simp only [decide_eq_true_eq]
  omega

/-! ## Limb and list helpers -/

/-- A limb read through `yLimbs`. -/
theorem yLimb_get {M : Nat → UInt8} {base n j : Nat} (hj : j < n) :
    (loadWord M (base + 32 * j)).toNat = (yLimbs M base n)[j]'(by simpa using hj) := by
  simp [yLimbs]

theorem yLimb_of_eq {M : Nat → UInt8} {base n j : Nat} (hj : j < n)
    {L : List Nat} (hL : yLimbs M base n = L) (hLj : j < L.length) :
    (loadWord M (base + 32 * j)).toNat = L[j] := by
  subst hL
  exact yLimb_get hj

/-- Total list access (0 out of range) — lets quantified limb facts avoid
index side conditions. -/
def lget (l : List Nat) (i : Nat) : Nat := l.getD i 0

theorem lget_eq {l : List Nat} {i : Nat} (h : i < l.length) : lget l i = l[i]'h := by
  simp [lget, h]

/-- A limb read stated through `lget`. -/
theorem yLimb_lget {M : Nat → UInt8} {base n j : Nat} (hj : j < n)
    {L : List Nat} (hL : yLimbs M base n = L) (hLj : j < L.length) :
    (loadWord M (base + 32 * j)).toNat = lget L j := by
  subst hL
  exact (yLimb_get hj).trans (lget_eq hLj).symm


/-- The head of a dropped suffix, as a concrete cons. -/
theorem drop_cons_of_lt : ∀ (l : List Nat) (i : Nat) (hi : i < l.length),
    l.drop i = l[i]'hi :: l.drop (i + 1) := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons a t ih =>
    intro i hi
    match i with
    | 0 => rfl
    | i + 1 =>
      have hi' : i < t.length := by simpa using hi
      simpa using ih i hi'

/-- The head of a dropped suffix is the dropped-to element. -/
theorem lget_drop_zero : ∀ (xs : List Nat) (i : Nat), i < xs.length →
    lget (xs.drop i) 0 = lget xs i := by
  intro xs
  induction xs with
  | nil => intro i hi; simp at hi
  | cons a t ih =>
    intro i hi
    match i with
    | 0 => rfl
    | i + 1 =>
      have hi' : i < t.length := by simpa using hi
      simpa [lget] using ih i hi'

/-- Position `length pre` of `pre ++ L` is the head of `L`. -/
theorem lget_append_len : ∀ (pre : List Nat) (L : List Nat),
    lget (pre ++ L) pre.length = lget L 0 := by
  intro pre
  induction pre with
  | nil => intro L; rfl
  | cons p t ih =>
    intro L
    simpa [lget, List.length_cons] using ih L

/-- Reading position `i` of `pre ++ xs.drop i` as `xs`'s `i`-th element. -/
theorem lget_append_drop {pre xs : List Nat} {i : Nat}
    (hlen : pre.length = i) (hxs : i < xs.length) :
    lget (pre ++ xs.drop i) i = lget xs i := by
  have h1 : lget (pre ++ xs.drop i) i = lget (pre ++ xs.drop i) pre.length := by
    rw [hlen]
  rw [h1, lget_append_len, lget_drop_zero xs i hxs]

/-- Setting position `length l₁` of `l₁ ++ x :: l₂`. -/
theorem set_append_mid {α : Type} {l₁ : List α} {x : α} {l₂ : List α} {z : α} :
    (l₁ ++ x :: l₂).set l₁.length z = l₁ ++ z :: l₂ := by
  induction l₁ with
  | nil => rfl
  | cons a t ih =>
    simp only [List.length_cons]
    exact congrArg (a :: ·) ih

/-- Setting position `i` of `l₁ ++ x :: l₂` when `length l₁ = i`. -/
theorem set_append_mid' {α : Type} {l₁ : List α} {x : α} {l₂ : List α} {z : α}
    {i : Nat} (h : l₁.length = i) : (l₁ ++ x :: l₂).set i z = l₁ ++ z :: l₂ := by
  subst h
  exact set_append_mid

/-- The `i`-th element is a member. -/
theorem mem_getElem {xs : List Nat} {i : Nat} (hi : i < xs.length) :
    xs[i]'hi ∈ xs := by
  induction xs generalizing i with
  | nil => cases hi
  | cons a t ih =>
    match i with
    | 0 => simp
    | i + 1 =>
      have hi' : i < t.length := by simpa using hi
      simpa using ih hi'

/-- `take` beyond the length is the whole list. -/
theorem take_eq_of_length : ∀ (l : List Nat) (n : Nat), l.length ≤ n → l.take n = l := by
  intro l
  induction l with
  | nil => intro n h; simp
  | cons a t ih =>
    intro n h
    match n with
    | 0 => simp at h
    | n + 1 => simpa using ih n (by simpa using h)

/-- `drop` beyond the length is empty. -/
theorem drop_eq_nil_of_length : ∀ (l : List Nat) (n : Nat), l.length ≤ n → l.drop n = [] := by
  intro l
  induction l with
  | nil => intro n h; simp
  | cons a t ih =>
    intro n h
    match n with
    | 0 => simp at h
    | n + 1 => simpa using ih n (by simpa using h)
/-! ## Value-level arithmetic -/

/-- One doubling round at the mod level. -/
theorem round_double (m a B r r2 : Nat)
    (hr : r = (a * B) % m) (hr2 : r2 = (r + r) % m) :
    r2 = (a * (2 * B)) % m := by
  have h2 : a * (2 * B) = a * B + a * B := by rw [Nat.two_mul, Nat.mul_add]
  rw [hr2, hr, h2]
  exact (Nat.add_mod (a * B) (a * B) m).symm

/-- Doubling plus a conditional add, at the mod level. -/
theorem round_bit (m a B r r2 rb : Nat) (bit : Nat)
    (hr : r = (a * B) % m) (hr2 : r2 = (r + r) % m)
    (hrb : rb = (r2 + bit * a) % m) :
    rb = (a * (2 * B + bit)) % m := by
  rw [hrb, hr2, hr,
    Nat.add_mod ((a * B % m + a * B % m) % m) (bit * a) m,
    Nat.mod_mod (a * B % m + a * B % m),
    ← Nat.add_mod (a * B) (a * B) m,
    ← Nat.add_mod (a * B + a * B) (bit * a) m,
    Nat.mul_comm bit a,
    show (a * B + a * B + a * bit) % m = a * (2 * B + bit) % m from by
      have h1 : a * (2 * B + bit) = a * B + a * B + a * bit := by
        rw [Nat.mul_add a (2 * B) bit, Nat.two_mul B, Nat.mul_add a B B]
      rw [h1]]

/-- `b / 2^(e-1) = 2 * (b / 2^e) + bit`, `bit` the bit at position `e-1`. -/
theorem div_step (b e : Nat) (he : 0 < e) :
    b / 2 ^ (e - 1) = 2 * (b / 2 ^ e) + (b / 2 ^ (e - 1)) % 2 := by
  have h1 : 2 ^ e = 2 ^ (e - 1) * 2 := by
    have hs : (2 : Nat) ^ e = 2 ^ (Nat.succ (e - 1)) := by
      congr 1; omega
    rw [hs, Nat.pow_succ]
  have hd1 := Nat.div_add_mod b (2 ^ (e - 1))
  have hd2 := Nat.div_add_mod b (2 ^ e)
  have hmod : b % 2 ^ e % 2 ^ (e - 1) = b % 2 ^ (e - 1) :=
    Nat.mod_mod_of_dvd b ⟨2, h1⟩
  have hdiv : b / 2 ^ (e - 1) / 2 = b / 2 ^ e := by
    rw [Nat.div_div_eq_div_mul b (2 ^ (e - 1)) 2, ← h1]
  have hbt : (b / 2 ^ (e - 1)) % 2 =
      b / 2 ^ (e - 1) - 2 * (b / 2 ^ (e - 1) / 2) := by
    have := Nat.div_add_mod (b / 2 ^ (e - 1)) 2
    omega
  omega

theorem hradius : radix = 2 ^ 256 := rfl

theorem radix_pos : 0 < radix := by
  have := radix_gt_one
  omega

/-- Limb `j` of a limb list, viewed through division. -/
theorem div_limb (bs : List Nat) (hlt : ∀ d ∈ bs, d < radix) (j : Nat) :
    Nat.ofDigits radix bs / 2 ^ (256 * j) % 2 ^ 256 = lget bs j := by
  induction j generalizing bs with
  | zero =>
    cases bs with
    | nil => simp [lget]
    | cons hd tl =>
      have hdlt : hd < radix := hlt hd (by simp)
      have hrad : (2 ^ 256 : Nat) = radix := hradius
      have h0 : lget (hd :: tl) 0 = hd := rfl
      rw [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.ofDigits_cons, hrad,
        Nat.add_mod hd (radix * Nat.ofDigits radix tl) radix,
        Nat.mul_mod_right radix (Nat.ofDigits radix tl),
        Nat.add_zero, Nat.mod_mod hd radix, Nat.mod_eq_of_lt hdlt, h0]
  | succ j ih =>
    cases bs with
    | nil => simp [lget]
    | cons hd tl =>
      have hdlt : hd < radix := hlt hd (by simp)
      have htl : ∀ d ∈ tl, d < radix := fun d hd' => hlt d (by simp [hd'])
      have hsplit : 2 ^ (256 * (j + 1)) = radix * 2 ^ (256 * j) := by
        rw [show 256 * (j + 1) = 256 * j + 256 from by ring, hradius,
          ← Nat.pow_add, Nat.add_comm]
      rw [Nat.ofDigits_cons, hsplit,
        ← Nat.div_div_eq_div_mul _ radix (2 ^ (256 * j)),
        Nat.add_mul_div_left _ _ radix_pos,
        Nat.div_eq_of_lt hdlt, Nat.zero_add]
      exact ih tl htl

/-- The top-bit seeding: below the top set bit, the divisor collapses. -/
theorem seed_top (L τ : Nat) (hτ : 2 ^ τ ≤ L) (hL : L < 2 ^ (τ + 1)) :
    L / 2 ^ τ = 1 := by
  have hp : 0 < 2 ^ τ := Nat.pow_pos (by omega)
  have hpow : 2 ^ (τ + 1) = 2 * 2 ^ τ := by
    rw [Nat.pow_succ]; omega
  have h1 : 1 ≤ L / 2 ^ τ := (Nat.one_le_div_iff hp).2 hτ
  have h2 : L / 2 ^ τ < 2 := (Nat.div_lt_iff_lt_mul hp).2 (by rw [← hpow]; exact hL)
  omega

/-- The machine's bit test on limb `L` agrees with the remaining multiplier's
parity. -/
theorem bit_bridge (b t hi L Q : Nat) (ht : t < 256)
    (hdecomp : b / 2 ^ (256 * hi) = L + 2 ^ 256 * Q) :
    (b / 2 ^ (256 * hi + t)) % 2 = (L / 2 ^ t) % 2 := by
  have hsplit : 2 ^ 256 = 2 ^ t * 2 ^ (256 - t) := by
    rw [← Nat.pow_add]; congr 1; omega
  have hdiv : b / 2 ^ (256 * hi + t) = L / 2 ^ t + 2 ^ (256 - t) * Q := by
    rw [show b / 2 ^ (256 * hi + t) = b / 2 ^ (256 * hi) / 2 ^ t from by
        rw [Nat.div_div_eq_div_mul b (2 ^ (256 * hi)) (2 ^ t), ← Nat.pow_add],
      hdecomp, hsplit, Nat.mul_assoc,
      Nat.add_mul_div_left _ _ (Nat.pow_pos (by omega))]
  have hKeven : 2 ^ (256 - t) * Q % 2 = 0 := by
    have h256 : 2 ^ (256 - t) = 2 ^ (255 - t) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [h256, Nat.mul_assoc, Nat.mul_left_comm]
    exact Nat.mul_mod_right _ _
  rw [hdiv, Nat.add_mod, hKeven, Nat.add_zero, Nat.mod_mod]

/-! ## The addMod scratch frame (for the call contract) -/
/-! ## The scratch frame -/

/-- The cells the addMod procedure call writes: the two address registers
plus its own eight scratch cells (matches
`Proof.AddModProcProof.addModCallScratch`). -/
def addModScratch : List Nat := [ADST, ASRC, C1, C2, I2, AOFF, AX, AY, AS, AZ]

theorem scratch_cells_lit : ∀ c ∈ [ADST, ASRC, C1, C2, I2, AOFF, AX, AY, AS, AZ],
    c ∈ fragCells := by
  decide

theorem arc_ne_lit : ∀ c ∈ [I2, C1, C2, AZ, AS, AY, AX, AOFF], c ≠ Ncell := by
  decide

theorem scratch_cells {c : Nat} (h : c ∈ addModScratch) : c ∈ fragCells := by
  unfold addModScratch at h
  exact scratch_cells_lit c h

/-- `M` agrees with `M₀` outside the `dst` and `SUBC` regions and the scratch
cells. -/
def AddModKeeps (M M₀ : Nat → UInt8) (dst n : Nat) : Prop :=
  ∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
    (∀ c ∈ addModScratch, a < c ∨ c + 32 ≤ a) → M a = M₀ a

/-- Writing inside the `dst` region keeps the frame. -/
theorem keeps_storeWord_dst {M M₀ : Nat → UInt8} {dst n q : Nat} {v : U256}
    (h : AddModKeeps M M₀ dst n) (hq : dst ≤ q ∧ q + 32 ≤ dst + 32 * n) :
    AddModKeeps (storeWord M q v) M₀ dst n := by
  intro a ha1 ha2 ha3
  have hd : a < q ∨ q + 32 ≤ a := by
    rcases ha1 with h1 | h1
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [storeWord_other hd]
  exact h a ha1 ha2 ha3

/-- Writing inside the `SUBC` region keeps the frame. -/
theorem keeps_storeWord_subc {M M₀ : Nat → UInt8} {dst n q : Nat} {v : U256}
    (h : AddModKeeps M M₀ dst n) (hq : SUBC ≤ q ∧ q + 32 ≤ SUBC + 32 * n) :
    AddModKeeps (storeWord M q v) M₀ dst n := by
  intro a ha1 ha2 ha3
  have hd : a < q ∨ q + 32 ≤ a := by
    rcases ha2 with h2 | h2
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  rw [storeWord_other hd]
  exact h a ha1 ha2 ha3

/-- Writing a scratch cell keeps the frame. -/
theorem keeps_storeWord_cell {M M₀ : Nat → UInt8} {dst n c : Nat} {v : U256}
    (h : AddModKeeps M M₀ dst n) (hc : c ∈ addModScratch) :
    AddModKeeps (storeWord M c v) M₀ dst n := by
  intro a ha1 ha2 ha3
  rw [storeWord_other (ha3 c hc)]
  exact h a ha1 ha2 ha3

/-- A region disjoint from the write set keeps its limbs. -/
theorem yLimbs_of_keeps {M M₀ : Nat → UInt8} {q dst n : Nat}
    (h : AddModKeeps M M₀ dst n)
    (hle : q + 32 * n ≤ dst ∨ dst + 32 * n ≤ q)
    (hqsub : q + 32 * n ≤ SUBC)
    (hqc : ∀ c ∈ addModScratch, q + 32 * n ≤ c) :
    yLimbs M q n = yLimbs M₀ q n := by
  rw [yLimbs_congr]
  intro a ha1 ha2
  refine h a ?_ ?_ ?_
  · omega
  · omega
  · intro c hc
    have := hqc c hc
    omega

/-- The trivial frame. -/
theorem keeps_refl (M : Nat → UInt8) (dst n : Nat) : AddModKeeps M M dst n := by
  intro a _ _ _
  rfl

/-! ## The mulMod frame -/
/-- The scratch cells the `mulMod` fragment writes besides its regions: its
own three registers plus the inlined `addMod` fragments' eight. -/
def mulModScratch : List Nat := [HIcell, T0, T1] ++ addModScratch

theorem mulScratch_cells {c : Nat} (h : c ∈ mulModScratch) : c ∈ fragCells := by
  unfold mulModScratch at h
  rcases List.mem_append.mp h with h | h
  · have hlit : ∀ c ∈ [HIcell, T0, T1], c ∈ fragCells := by decide
    exact hlit c h
  · exact scratch_cells h

theorem mulScratch_ge_Ncell {c : Nat} (h : c ∈ mulModScratch) : Ncell ≤ c :=
  fragCells_ge c (mulScratch_cells h)

theorem mulScratch_add {c : Nat} (h : c ∈ addModScratch) : c ∈ mulModScratch :=
  List.mem_append.mpr (Or.inr h)

/-- The mulMod frame: every byte outside the OUT, ACC, SUBC regions and the
scratch cells is unchanged. -/
def MulModKeeps (M M₀ : Nat → UInt8) (n : Nat) : Prop :=
  ∀ a, (a < OUT ∨ OUT + 32 * n ≤ a) → (a < ACC ∨ ACC + 32 * n ≤ a) →
    (a < SUBC ∨ SUBC + 32 * n ≤ a) → (∀ c ∈ mulModScratch, a < c ∨ c + 32 ≤ a) →
    M a = M₀ a

theorem mulKeeps_refl (M : Nat → UInt8) (n : Nat) : MulModKeeps M M n := by
  intro _ _ _ _ _
  rfl

theorem mulKeeps_trans {M₁ M₂ M₀ : Nat → UInt8} {n : Nat}
    (h₁ : MulModKeeps M₁ M₂ n) (h₂ : MulModKeeps M₂ M₀ n) : MulModKeeps M₁ M₀ n :=
  fun a ha1 ha2 ha3 ha4 => (h₁ a ha1 ha2 ha3 ha4).trans (h₂ a ha1 ha2 ha3 ha4)

/-- A word write inside one of the three regions or a scratch cell keeps the
frame. -/
theorem mulKeeps_storeWord {M M₀ : Nat → UInt8} {n q : Nat} {v : U256}
    (h : MulModKeeps M M₀ n)
    (hq : (OUT ≤ q ∧ q + 32 ≤ OUT + 32 * n) ∨ (ACC ≤ q ∧ q + 32 ≤ ACC + 32 * n) ∨
      (SUBC ≤ q ∧ q + 32 ≤ SUBC + 32 * n) ∨ q ∈ mulModScratch) :
    MulModKeeps (storeWord M q v) M₀ n := by
  intro a ha1 ha2 ha3 ha4
  have hdisj : a < q ∨ q + 32 ≤ a := by
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | hq
    · rcases ha1 with ha | ha <;> omega
    · rcases ha2 with ha | ha <;> omega
    · rcases ha3 with ha | ha <;> omega
    · rcases ha4 q hq with ha | ha <;> omega
  rw [storeWord_other hdisj]
  exact h a ha1 ha2 ha3 ha4

/-- An `addMod` frame on `OUT` implies the `mulMod` frame. -/
theorem mulKeeps_of_add {M M₀ : Nat → UInt8} {n : Nat}
    (h : AddModKeeps M M₀ OUT n) : MulModKeeps M M₀ n :=
  fun a ha1 _ha2 ha3 ha4 => h a ha1 ha3 (fun c hc => ha4 c (mulScratch_add hc))

/-- A region clear of the write set keeps its limbs. -/
theorem yLimbs_of_mulKeeps {M M₀ : Nat → UInt8} {q n : Nat} (h : MulModKeeps M M₀ n)
    (h1 : q + 32 * n ≤ OUT ∨ OUT + 32 * n ≤ q)
    (h2 : q + 32 * n ≤ ACC ∨ ACC + 32 * n ≤ q)
    (h3 : q + 32 * n ≤ SUBC ∨ SUBC + 32 * n ≤ q)
    (hqN : q + 32 * n ≤ Ncell) :
    yLimbs M q n = yLimbs M₀ q n := by
  rw [yLimbs_congr]
  intro a ha1 ha2
  refine h a ?_ ?_ ?_ (fun c hc => ?_)
  · rcases h1 with h | h <;> omega
  · rcases h2 with h | h <;> omega
  · rcases h3 with h | h <;> omega
  · have hge := mulScratch_ge_Ncell hc
    omega

/-- A word outside the write set is unchanged. -/
theorem loadWord_of_mulKeeps {M M₀ : Nat → UInt8} {q n : Nat} (h : MulModKeeps M M₀ n)
    (h1 : q + 32 ≤ OUT ∨ OUT + 32 * n ≤ q)
    (h2 : q + 32 ≤ ACC ∨ ACC + 32 * n ≤ q)
    (h3 : q + 32 ≤ SUBC ∨ SUBC + 32 * n ≤ q)
    (h4 : ∀ c ∈ mulModScratch, q + 32 ≤ c ∨ c + 32 ≤ q) :
    loadWord M q = loadWord M₀ q := by
  rw [loadWord_congr]
  intro a ha1 ha2
  refine h a ?_ ?_ ?_ ?_
  · rcases h1 with h | h <;> omega
  · rcases h2 with h | h <;> omega
  · rcases h3 with h | h <;> omega
  · intro c hc
    rcases h4 c hc with h | h <;> omega

/-! ## The procedure's labels, body fragments, and suffixes -/

/-- Every label the `mulModBig` procedure uses: its entry and ten internal
jump targets, its two `addMod`-call return labels, and the `addMod`
procedure's entry. -/
structure MulModProcLabels where
  lmmEntry : Nat
  lScanTop : Nat
  lTopBit : Nat
  lCopy : Nat
  lBits : Nat
  lNextLimb : Nat
  lZero : Nat
  lZeroLoop : Nat
  lDone : Nat
  lRetCopy : Nat
  lExit : Nat
  lSqRet : Nat
  lAddRet : Nat
  lamEntry : Nat

/-- One `addMod` procedure call as it appears inside `mulModProc`:
set the `ADST`/`ASRC` argument cells, push the return label, jump to the
procedure entry, with the return label right after the jump. -/
def mmCallSite (dst src lret lamEntry : Nat) : List Asm :=
  store ADST (.imm dst) ++ store ASRC (.imm src) ++
  [.pushLabel lret, .jump lamEntry, .label lret]

/-- The scan loop top: walk `HI` down past zero limbs of the `BPTR`-cell
region. -/
def mulModScanTopBody (l : MulModProcLabels) : List Asm :=
  jumpIfZ (.load HIcell) l.lZero ++
  store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
  jumpIfZ (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell))))
    l.lScanTop ++
  store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
  store T1 (.imm 256)

/-- The top-bit scan: decrement `T1` until the bit is set. -/
def mulModTopBitBody (l : MulModProcLabels) : List Asm :=
  store T1 (.bin .sub (.load T1) (.imm 1)) ++
  jumpIfZ (bitTestOf T0 T1) l.lTopBit ++
  store I2 (.imm 0)

/-- The copy-in loop body: `dst[i] := src[i]`, exiting to `lExit`. -/
def mulModCopyBody (dstBase srcBase : Nat) (lExit : Label) (l : MulModProcLabels) : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) lExit ++
  storeAt (.bin .add (.imm dstBase) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm srcBase) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lCopy]

/-- The bits loop body: consume one bit of the multiplier, calling the
`addMod` procedure for the doubling and the conditional add. -/
def mulModBitsBody (l : MulModProcLabels) : List Asm :=
  jumpIfZ (.load T1) l.lNextLimb ++
  store T1 (.bin .sub (.load T1) (.imm 1)) ++
  mmCallSite OUT OUT l.lSqRet l.lamEntry ++
  jumpIfZ (bitTestOf T0 T1) l.lBits ++
  mmCallSite OUT ACC l.lAddRet l.lamEntry ++
  [.jump l.lBits]

/-- The limb transition. -/
def mulModNextLimbBody (l : MulModProcLabels) : List Asm :=
  jumpIfZ (.load HIcell) l.lDone ++
  store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
  store T1 (.imm 256) ++
  store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
  [.jump l.lBits]

/-- The `b = 0` path entry. -/
def mulModZeroEntry : List Asm := store I2 (.imm 0)

/-- The zero loop body: `OUT[i] := 0`. -/
def mulModZeroLoopBody (l : MulModProcLabels) : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) l.lDone ++
  storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2))) (.imm 0) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lZeroLoop]

/-- The return-copy entry and loop body: `ACC[i] := OUT[i]`. -/
def mulModRetEntry : List Asm := store I2 (.imm 0)

def mulModRetCopyBody (l : MulModProcLabels) : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) l.lExit ++
  storeAt (.bin .add (.imm ACC) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lRetCopy]

/-- Fragment suffixes, from each label to the trailing `.dynJump`. -/
def mulModFromTopBit (l : MulModProcLabels) : List Asm :=
  [.label l.lTopBit] ++ mulModTopBitBody l ++ [.label l.lCopy] ++
  mulModCopyBody OUT ACC l.lBits l ++ [.label l.lBits] ++ mulModBitsBody l ++
  [.label l.lNextLimb] ++ mulModNextLimbBody l ++ [.label l.lZero] ++
  mulModZeroEntry ++ [.label l.lZeroLoop] ++ mulModZeroLoopBody l ++
  [.label l.lDone] ++ mulModRetEntry ++ [.label l.lRetCopy] ++
  mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

def mulModFromCopy (l : MulModProcLabels) : List Asm :=
  [.label l.lBits] ++ mulModBitsBody l ++
  [.label l.lNextLimb] ++ mulModNextLimbBody l ++ [.label l.lZero] ++
  mulModZeroEntry ++ [.label l.lZeroLoop] ++ mulModZeroLoopBody l ++
  [.label l.lDone] ++ mulModRetEntry ++ [.label l.lRetCopy] ++
  mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

def mulModFromBits (l : MulModProcLabels) : List Asm :=
  mulModBitsBody l ++
  [.label l.lNextLimb] ++ mulModNextLimbBody l ++ [.label l.lZero] ++
  mulModZeroEntry ++ [.label l.lZeroLoop] ++ mulModZeroLoopBody l ++
  [.label l.lDone] ++ mulModRetEntry ++ [.label l.lRetCopy] ++
  mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

def mulModFromNextLimb (l : MulModProcLabels) : List Asm :=
  mulModNextLimbBody l ++ [.label l.lZero] ++
  mulModZeroEntry ++ [.label l.lZeroLoop] ++ mulModZeroLoopBody l ++
  [.label l.lDone] ++ mulModRetEntry ++ [.label l.lRetCopy] ++
  mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

def mulModFromZero (l : MulModProcLabels) : List Asm :=
  mulModZeroEntry ++ [.label l.lZeroLoop] ++ mulModZeroLoopBody l ++
  [.label l.lDone] ++ mulModRetEntry ++ [.label l.lRetCopy] ++
  mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

def mulModFromZeroLoop (l : MulModProcLabels) : List Asm :=
  mulModZeroLoopBody l ++ [.label l.lDone] ++ mulModRetEntry ++
  [.label l.lRetCopy] ++ mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

/-- The code from the `lDone` label to the trailing `.dynJump`. -/
def mulModFromRet (l : MulModProcLabels) : List Asm :=
  mulModRetEntry ++ [.label l.lRetCopy] ++ mulModRetCopyBody l ++
  [.label l.lExit] ++ [.dynJump]

def mulModFromRetCopy (l : MulModProcLabels) : List Asm :=
  mulModRetCopyBody l ++ [.label l.lExit] ++ [.dynJump]

/-- The procedure body: the code from just after `.label lmmEntry`. -/
def mulModProcBody (l : MulModProcLabels) : List Asm :=
  store HIcell (.load Ncell) ++ [.label l.lScanTop] ++
  mulModScanTopBody l ++ mulModFromTopBit l

theorem mulModProcBody_split (l : MulModProcLabels) :
    mulModProcBody l =
  store HIcell (.load Ncell) ++ [.label l.lScanTop] ++
  mulModScanTopBody l ++ mulModFromTopBit l := rfl

/-! ## Machine-level helpers -/

theorem hI2EqM : I2 = 0x1e60 := rfl

/-- The relaxed pinning threshold: the program's big path pins
`activeWords = 250`, whose window is exactly `TOP + 32 = 0x1f40` bytes, so
`0x1f40` would be unsatisfiable at every real big-path state.  Every fragment
cell lies at or below `TOP`, so `0x1f40` suffices for all pinning. -/
theorem haw_pin {S : EvmState} (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    {c : Nat} (hc : c ∈ fragCells) :
    c < 2 ^ 256 ∧ c + 32 ≤ 32 * S.activeWords.toNat := by
  have hmem : c ≤ TOP := fragCells_le c hc
  have htop : (TOP : Nat) = 0x1f20 := rfl
  have hpin : ((TOP : Nat) + 32 : Nat) = 0x1f40 := rfl
  have hlt : (TOP : Nat) < 2 ^ 256 := TOP_lt
  constructor <;> omega

/-- `exprOK` for a cell load under the relaxed pin. -/
theorem exprOK_load_cell' {S : EvmState} (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    {c : Nat} (hc : c ∈ fragCells) : exprOK (.load c) S := haw_pin haw hc

/-- The `I2 < Ncell` exit test of a limb loop, fall-through (`i < n`). -/
theorem exitTest_fall' [model : ExternalModel] {prog : List Asm} {l : Label}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    {i n : Nat} (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hN : (loadWord yst.memory Ncell).toNat = n)
    (hI2 : (loadWord yst.memory I2).toNat = i)
    (hn : n ≤ 2 ^ 255) (hlt : i < n) :
    ASteps prog ⟨jumpUnlessLt (.load I2) (.load Ncell) l ++ k, σ, yst⟩ ⟨k, σ, yst⟩ := by
  have hI2w : loadWord yst.memory I2 = BitVec.ofNat 256 i :=
    word_of_toNat hI2 (by omega)
  have hNw : loadWord yst.memory Ncell = BitVec.ofNat 256 n :=
    word_of_toNat hN (by omega)
  exact jumpUnlessLt_val_fall
    (by rw [show evalExpr (.load I2) yst = loadWord yst.memory I2 from rfl, hI2w])
    (by rw [show evalExpr (.load Ncell) yst = loadWord yst.memory Ncell from rfl, hNw])
    (exprOK_load_cell' haw (by simp [fragCells]))
    (exprOK_load_cell' haw (by simp [fragCells])) (by omega) (by omega) hlt

/-- The `I2 < Ncell` exit test of a limb loop, taken (`n ≤ i`). -/
theorem exitTest_taken' [model : ExternalModel] {prog : List Asm} {l : Label}
    {c' k : List Asm} {σ : List AVal} {yst : EvmState}
    {i n : Nat} (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hN : (loadWord yst.memory Ncell).toNat = n)
    (hI2 : (loadWord yst.memory I2).toNat = i)
    (hn : n ≤ 2 ^ 255)
    (hle : n ≤ i)
    (hfind : findLabel l prog = some c') :
    ASteps prog ⟨jumpUnlessLt (.load I2) (.load Ncell) l ++ k, σ, yst⟩ ⟨c', σ, yst⟩ := by
  have hI2w : loadWord yst.memory I2 = BitVec.ofNat 256 i :=
    word_of_toNat hI2 (by omega)
  have hNw : loadWord yst.memory Ncell = BitVec.ofNat 256 n :=
    word_of_toNat hN (by omega)
  exact jumpUnlessLt_val_taken
    (by rw [show evalExpr (.load I2) yst = loadWord yst.memory I2 from rfl, hI2w])
    (by rw [show evalExpr (.load Ncell) yst = loadWord yst.memory Ncell from rfl, hNw])
    (exprOK_load_cell' haw (by simp [fragCells]))
    (exprOK_load_cell' haw (by simp [fragCells])) (by omega) (by omega) hle hfind
/-- Address `base + 32 * (cell value)` as an `ofNat` word. -/
theorem eval_addr32 {S : EvmState} {base c k : Nat}
    (hw : loadWord S.memory c = BitVec.ofNat 256 k) :
    evalExpr (.bin .add (.imm base) (.bin .mul (.imm 32) (.load c))) S =
      BitVec.ofNat 256 (base + 32 * k) := by
  simp only [evalExpr, evalBin, hw, ofNat_mul256, ofNat_add256]

/-- Address `bptr + 32 * HI` as an `ofNat` word. -/
theorem eval_addr_hi {S : EvmState} {bptr h : Nat}
    (hw : loadWord S.memory HIcell = BitVec.ofNat 256 h) :
    evalExpr (.bin .add (.imm bptr) (.bin .mul (.imm 32) (.load HIcell))) S =
      BitVec.ofNat 256 (bptr + 32 * h) :=
  eval_addr32 hw

/-- An `mload` at `base + 32 * (cell value)`. -/
theorem eval_mload32 {S : EvmState} {base c k : Nat}
    (hw : loadWord S.memory c = BitVec.ofNat 256 k)
    (hlt : base + 32 * k < 2 ^ 256) :
    evalExpr (loadAt (.bin .add (.imm base) (.bin .mul (.imm 32) (.load c)))) S =
      loadWord S.memory (base + 32 * k) := by
  show loadWord S.memory (evalExpr
      (.bin .add (.imm base) (.bin .mul (.imm 32) (.load c))) S).toNat = _
  rw [eval_addr32 hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The limb load at `bptr + 32 * HI`. -/
theorem eval_loadAt_hi {S : EvmState} {bptr h : Nat}
    (hw : loadWord S.memory HIcell = BitVec.ofNat 256 h)
    (hlt : bptr + 32 * h < 2 ^ 256) :
    evalExpr (loadAt (.bin .add (.imm bptr) (.bin .mul (.imm 32) (.load HIcell)))) S =
      loadWord S.memory (bptr + 32 * h) := by
  show loadWord S.memory (evalExpr
      (.bin .add (.imm bptr) (.bin .mul (.imm 32) (.load HIcell))) S).toNat = _
  rw [eval_addr_hi hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- Bit-test evaluation on computed words. -/
theorem toNat_bitTestOf {S : EvmState} {t : Nat} {x : U256}
    (hT0 : loadWord S.memory T0 = x)
    (hT1 : loadWord S.memory T1 = BitVec.ofNat 256 t)
    (ht : t < 2 ^ 16) :
    (evalExpr (bitTestOf T0 T1) S).toNat = x.toNat / 2 ^ t % 2 := by
  have h1 : evalExpr (bitTestOf T0 T1) S
      = (x >>> (BitVec.ofNat 256 t).toNat) &&& BitVec.ofNat 256 1 := by
    simp only [bitTestOf, evalExpr, evalBin, hT0, hT1]
  have hsh : (x >>> t).toNat = x.toNat / 2 ^ t := by
    rw [BitVec.toNat_ushiftRight x t, Nat.shiftRight_eq_div_pow]
  have hmodt : t % 2 ^ 256 = t :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ht
      (Nat.pow_le_pow_right (by omega) (by omega : 16 ≤ 256)))
  have hone : (BitVec.ofNat 256 1).toNat = 1 := by decide
  rw [h1, BitVec.toNat_and, BitVec.toNat_ofNat, hmodt, hone, hsh]
  simp

/-- Address `bptr + 32 * HI` read through the `BPTR` cell. -/
theorem eval_addr_bptr {S : EvmState} {bptr h : Nat}
    (hwB : loadWord S.memory BPTR = BitVec.ofNat 256 bptr)
    (hw : loadWord S.memory HIcell = BitVec.ofNat 256 h) :
    evalExpr (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell))) S =
      BitVec.ofNat 256 (bptr + 32 * h) := by
  simp only [evalExpr, evalBin, hwB, hw, ofNat_mul256, ofNat_add256]

/-- The limb load at `bptr + 32 * HI`, through the `BPTR` cell. -/
theorem eval_loadAt_bptr {S : EvmState} {bptr h : Nat}
    (hwB : loadWord S.memory BPTR = BitVec.ofNat 256 bptr)
    (hw : loadWord S.memory HIcell = BitVec.ofNat 256 h)
    (hlt : bptr + 32 * h < 2 ^ 256) :
    evalExpr (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) S =
      loadWord S.memory (bptr + 32 * h) := by
  show loadWord S.memory (evalExpr
      (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell))) S).toNat = _
  rw [eval_addr_bptr hwB hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The word value of the `BPTR` cell. -/
theorem BPTR_word {S : EvmState} {bptr : Nat}
    (h : (loadWord S.memory BPTR).toNat = bptr) (hlt : bptr < 2 ^ 256) :
    loadWord S.memory BPTR = BitVec.ofNat 256 bptr :=
  word_of_toNat h hlt


/-- `I2 := I2 + 1` (adapting AddModProof's increment round step). -/
theorem mulIncr_steps [model : ExternalModel] {prog : List Asm} {i : Nat}
    {k : List Asm} {σ : List AVal} {S : EvmState}
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hI2 : (loadWord S.memory I2).toNat = i) :
    ASteps prog
      ⟨store I2 (.bin .add (.load I2) (.imm 1)) ++ k, σ, S⟩
      ⟨k, σ, {S with memory :=
        (storeWord S.memory I2 (BitVec.ofNat 256 (i + 1)))}⟩ := by
  have hi256 : i < 2 ^ 256 := by omega
  have hI2w : loadWord S.memory I2 = BitVec.ofNat 256 i :=
    word_of_toNat hI2 hi256
  have hev : evalExpr (.bin .add (.load I2) (.imm 1)) S
      = BitVec.ofNat 256 (i + 1) := by
    simp only [evalExpr, evalBin, hI2w, ofNat_add256]
  exact store_cell_val (c := I2) (e := .bin .add (.load I2) (.imm 1))
    (w := BitVec.ofNat 256 (i + 1)) hev
    ⟨rfl, exprOK_load_cell' haw (by simp [fragCells]), True.intro⟩
    (haw_pin haw (by simp [fragCells]))

/-! ## The region-copy loop -/
/-! ## The region-copy loop -/

/-- One round of `dstBase[i] := srcBase[i]`. -/
theorem mulCopyRound_steps [model : ExternalModel] {prog : List Asm}
    (dstBase srcBase : Nat) (l : MulModProcLabels) (xs out₀ : List Nat) (n i : Nat)
    {k : List Asm} {σ : List AVal} {S : EvmState}
    (hCopy : findLabel l.lCopy prog =
      some (mulModCopyBody dstBase srcBase lExit l ++ k))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hi : i < n) (hn32 : n ≤ 32)
    (hdstN : dstBase + 32 * n ≤ Ncell) (hsrcN : srcBase + 32 * n ≤ Ncell)
    (hds : dstBase + 32 * n ≤ srcBase ∨ srcBase + 32 * n ≤ dstBase)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = i)
    (hdstL : yLimbs S.memory dstBase n = xs.take i ++ out₀.drop i)
    (hsrcL : yLimbs S.memory srcBase n = xs)
    (hxslen : xs.length = n) (houtlen : out₀.length = n)
    (hxd : lget xs i < radix) :
    ∃ S', ASteps prog ⟨mulModCopyBody dstBase srcBase lExit l ++ k, σ, S⟩
        ⟨mulModCopyBody dstBase srcBase lExit l ++ k, σ, S'⟩ ∧
      (loadWord S'.memory I2).toNat = i + 1 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      yLimbs S'.memory dstBase n = xs.take (i + 1) ++ out₀.drop (i + 1) ∧
      yLimbs S'.memory srcBase n = xs ∧
      (∀ a, (a < dstBase ∨ dstBase + 32 * n ≤ a) →
        (a < I2 ∨ I2 + 32 ≤ a) → S'.memory a = S.memory a) ∧
      S'.activeWords = S.activeWords ∧ S'.env = S.env := by
  have hI2c : I2 = 0x1e60 := rfl
  have hi256 : i < 2 ^ 256 := by omega
  have hI2w : loadWord S.memory I2 = BitVec.ofNat 256 i := word_of_toNat hI2 hi256
  have hxslen' : i < xs.length := by omega
  have hxsi : (loadWord S.memory (srcBase + 32 * i)).toNat = lget xs i :=
    (yLimb_of_eq hi hsrcL hxslen').trans (lget_eq hxslen').symm
  have hxlt : lget xs i < 2 ^ 256 := by
    rw [hradius] at hxd; omega
  have hxw : loadWord S.memory (srcBase + 32 * i) = BitVec.ofNat 256 (lget xs i) :=
    word_of_toNat hxsi hxlt
  set S₁ : EvmState := {S with memory :=
      (storeWord S.memory (dstBase + 32 * i)
        (loadWord S.memory (srcBase + 32 * i)))} with hS₁def
  have hS₁mem : S₁.memory =
      storeWord S.memory (dstBase + 32 * i) (loadWord S.memory (srcBase + 32 * i)) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hI2₁ : (loadWord S₁.memory I2).toNat = i := by
    rw [hS₁mem, loadWord_storeWord_disj (p := dstBase + 32 * i) (q := I2)
      (show dstBase + 32 * i + 32 ≤ I2 ∨ I2 + 32 ≤ dstBase + 32 * i by
        have := fragCells_ge I2 (by simp [fragCells])
        omega)]
    exact hI2
  have hI2w₁ : loadWord S₁.memory I2 = BitVec.ofNat 256 i :=
    word_of_toNat hI2₁ hi256
  set S₂ : EvmState := {S₁ with memory :=
      (storeWord S₁.memory I2 (BitVec.ofNat 256 (i + 1)))} with hS₂def
  have hS₂mem : S₂.memory = storeWord S₁.memory I2 (BitVec.ofNat 256 (i + 1)) := rfl
  have hsteps : ASteps prog ⟨mulModCopyBody dstBase srcBase lExit l ++ k, σ, S⟩
      ⟨mulModCopyBody dstBase srcBase lExit l ++ k, σ, S₂⟩ := by
    rw [show mulModCopyBody dstBase srcBase lExit l =
        jumpUnlessLt (.load I2) (.load Ncell) lExit ++
        storeAt (.bin .add (.imm dstBase) (.bin .mul (.imm 32) (.load I2)))
          (loadAt (.bin .add (.imm srcBase) (.bin .mul (.imm 32) (.load I2)))) ++
        store I2 (.bin .add (.load I2) (.imm 1)) ++ [.jump l.lCopy] from rfl]
    refine (exitTest_fall' (prog := prog) (l := lExit) haw hN hI2 (by omega) hi).trans ?_
    have hncellEq : Ncell = 0x1cc0 := rfl
    refine (storeAt_val (prog := prog)
      (addrE := .bin .add (.imm dstBase) (.bin .mul (.imm 32) (.load I2)))
      (valE := loadAt (.bin .add (.imm srcBase) (.bin .mul (.imm 32) (.load I2))))
      (addr := dstBase + 32 * i) (w := loadWord S.memory (srcBase + 32 * i))
      (eval_addr32 (base := dstBase) (c := I2) hI2w)
      (eval_mload32 (base := srcBase) (c := I2) hI2w (by omega))
      (by omega)
      ⟨by
        show (evalExpr (.bin .add (.imm srcBase)
            (.bin .mul (.imm 32) (.load I2))) S).toNat
            + 32 ≤ 32 * S.activeWords.toNat
        rw [eval_addr32 (base := srcBase) (c := I2) hI2w, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show srcBase + 32 * i < 2 ^ 256 by omega)]
        omega,
        ⟨rfl, True.intro, ⟨rfl, True.intro,
          exprOK_load_cell' haw (by simp [fragCells])⟩⟩⟩
      ⟨rfl, True.intro, ⟨rfl, True.intro,
        exprOK_load_cell' haw (by simp [fragCells])⟩⟩
      (by
        show dstBase + 32 * i + 32 ≤ 32 * S.activeWords.toNat
        omega)).trans ?_
    refine (mulIncr_steps (prog := prog) (S := S₁) hawS₁ hI2₁).trans ?_
    exact ASteps.single (astep_jump hCopy)
  refine ⟨S₂, hsteps, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · rw [hS₂mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 256)]
  · have hNc : loadWord S₂.memory Ncell = loadWord S.memory Ncell := by
      rw [hS₂mem, hS₁mem]
      rw [loadWord_storeWord_disj (p := I2) (q := Ncell)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
        loadWord_storeWord_disj (p := dstBase + 32 * i) (q := Ncell)
        (Or.inl (show dstBase + 32 * i + 32 ≤ Ncell by omega))]
    rw [hNc]; exact hN
  · have houtlen' : i < out₀.length := by omega
    have htk : xs.take (i + 1) = xs.take i ++ [xs[i]'hxslen'] := by
      simp [List.take_add_one]
    rw [hS₂mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₁mem,
      yLimbs_storeWord S.memory dstBase n i hi
        (loadWord S.memory (srcBase + 32 * i)),
      show (loadWord S.memory (srcBase + 32 * i)).toNat = xs[i]'hxslen' from by
        rw [hxsi, lget_eq hxslen'],
      hdstL, drop_cons_of_lt out₀ i houtlen',
      set_append_mid' (show (xs.take i).length = i from by
        simp only [List.length_take, hxslen]; omega)]
    rw [htk, List.append_assoc]
    rfl
  · rw [hS₂mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₁mem]
    rcases hds with h | h
    · rw [yLimbs_storeWord_disjoint (q := dstBase + 32 * i) (Or.inl (by omega))]
      exact hsrcL
    · rw [yLimbs_storeWord_disjoint (q := dstBase + 32 * i) (Or.inr (by omega))]
      exact hsrcL
  · intro a ha1 ha2
    have hstep2 : S₂.memory a = S₁.memory a :=
      storeWord_other (p := I2) (a := a)
        (show a < I2 ∨ I2 + 32 ≤ a by
          rcases ha2 with h | h
          · omega
          · omega)
    have hstep1 : S₁.memory a = S.memory a :=
      storeWord_other (p := dstBase + 32 * i) (a := a)
        (show a < dstBase + 32 * i ∨ dstBase + 32 * i + 32 ≤ a by
          rcases ha1 with h | h
          · omega
          · omega)
    rw [hstep2, hstep1]

/-- The full copy loop: from `I2 = 0` to the exit label. -/
theorem mulCopyLoop_steps [model : ExternalModel] {prog : List Asm}
    (dstBase srcBase : Nat) (l : MulModProcLabels) (xs out₀ : List Nat) (n : Nat)
    {lExit : Label} {c' k : List Asm} {σ : List AVal} {S : EvmState}
    (hCopy : findLabel l.lCopy prog =
      some (mulModCopyBody dstBase srcBase lExit l ++ k))
    (hExit : findLabel lExit prog = some c')
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hdstN : dstBase + 32 * n ≤ Ncell) (hsrcN : srcBase + 32 * n ≤ Ncell)
    (hds : dstBase + 32 * n ≤ srcBase ∨ srcBase + 32 * n ≤ dstBase)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = 0)
    (hdstL : yLimbs S.memory dstBase n = out₀)
    (hsrcL : yLimbs S.memory srcBase n = xs)
    (hxslen : xs.length = n) (houtlen : out₀.length = n)
    (hxd : ∀ d ∈ xs, d < radix) :
    ∃ S', ASteps prog ⟨mulModCopyBody dstBase srcBase lExit l ++ k, σ, S⟩
        ⟨c', σ, S'⟩ ∧
      yLimbs S'.memory dstBase n = xs ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      yLimbs S'.memory srcBase n = xs ∧
      (∀ a, (a < dstBase ∨ dstBase + 32 * n ≤ a) →
        (a < I2 ∨ I2 + 32 ≤ a) → S'.memory a = S.memory a) ∧
      S'.activeWords = S.activeWords ∧ S'.env = S.env := by
  have hyL : ∀ (i : Nat), i < n → lget xs i < radix := by
    intro i hi
    have himem : xs[i]'(show i < xs.length by omega) ∈ xs :=
      mem_getElem (show i < xs.length by omega)
    rw [lget_eq (show i < xs.length by omega)]
    exact hxd _ himem
  have hawSelf : 0x1f40 ≤ 32 * S.activeWords.toNat := haw
  obtain ⟨S', hP, hsteps⟩ :=
    loop_counted (model := model) (prog := prog)
      (top := mulModCopyBody dstBase srcBase lExit l ++ k)
      (σ := σ) (c' := c')
      (Inv := fun St m => ∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        yLimbs St.memory dstBase n = xs.take i ++ out₀.drop i ∧
        yLimbs St.memory srcBase n = xs ∧
        (∀ a, (a < dstBase ∨ dstBase + 32 * n ≤ a) →
          (a < I2 ∨ I2 + 32 ≤ a) → St.memory a = S.memory a) ∧
        St.activeWords = S.activeWords ∧ St.env = S.env)
      (P := fun St => yLimbs St.memory dstBase n = xs ∧
        (loadWord St.memory Ncell).toNat = n ∧
        yLimbs St.memory srcBase n = xs ∧
        (∀ a, (a < dstBase ∨ dstBase + 32 * n ≤ a) →
          (a < I2 ∨ I2 + 32 ≤ a) → St.memory a = S.memory a) ∧
        St.activeWords = S.activeWords ∧ St.env = S.env)
      (fun {m St} _hmpos hm => by
        rcases hm with ⟨i, hI2i, him, hNst, hdstst, hsrcst, hkeepst, hawEq, henvEq⟩
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exact absurd hm0 (by omega)
        · left
          have hin : i < n := by omega
          have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
            rw [hawEq]; exact haw
          obtain ⟨S', hsteps, hI2', hN', hdst', hsrc', hkeeps', hawEq', henvEq'⟩ :=
            mulCopyRound_steps (dstBase := dstBase) (srcBase := srcBase) (l := l)
              (xs := xs) (out₀ := out₀) (n := n) (i := i) (k := k) hCopy hawSt
              hin hn32 hdstN hsrcN hds hNst hI2i hdstst hsrcst hxslen houtlen
              (hyL i hin)
          have hawEq'' : S'.activeWords = S.activeWords := by rw [hawEq', hawEq]
          have hkeeps'' : ∀ a, (a < dstBase ∨ dstBase + 32 * n ≤ a) →
              (a < I2 ∨ I2 + 32 ≤ a) → S'.memory a = S.memory a := by
            intro a ha1 ha2
            exact (hkeeps' a ha1 ha2).trans (hkeepst a ha1 ha2)
          exact ⟨S', ⟨i + 1, hI2', by omega, hN', hdst', hsrc', hkeeps'',
            hawEq'', henvEq'.trans henvEq⟩, hsteps⟩)
      (fun St hm => by
        rcases hm with ⟨i, hI2i, him, hNst, hdstst, hsrcst, hkeepst, hawEq, henvEq⟩
        have hI2n : i = n := by omega
        rw [hI2n, take_eq_of_length xs n (by omega : xs.length ≤ n),
          drop_eq_nil_of_length out₀ n (by omega : out₀.length ≤ n),
          List.append_nil] at hdstst
        refine ⟨⟨hdstst, hNst, hsrcst, hkeepst, hawEq, henvEq⟩, ?_⟩
        rw [show mulModCopyBody dstBase srcBase lExit l =
            jumpUnlessLt (.load I2) (.load Ncell) lExit ++
            storeAt (.bin .add (.imm dstBase) (.bin .mul (.imm 32) (.load I2)))
              (loadAt (.bin .add (.imm srcBase) (.bin .mul (.imm 32) (.load I2)))) ++
            store I2 (.bin .add (.load I2) (.imm 1)) ++ [.jump l.lCopy] from rfl]
        exact exitTest_taken' (model := model) (prog := prog) (l := lExit)
          (k := storeAt (.bin .add (.imm dstBase) (.bin .mul (.imm 32) (.load I2)))
              (loadAt (.bin .add (.imm srcBase) (.bin .mul (.imm 32) (.load I2)))) ++
            store I2 (.bin .add (.load I2) (.imm 1)) ++ [.jump l.lCopy] ++ k)
          (by rw [hawEq]; exact haw) hNst hI2i
          (by omega) (by omega) hExit)
      (n := n) (yst := S)
      ⟨0, hI2, by omega, hN, by
        rw [show xs.take 0 = [] from rfl, show out₀.drop 0 = out₀ from rfl]
        exact hdstL, hsrcL,
        fun _ _ _ => rfl, rfl, rfl⟩
  obtain ⟨hdst', hN', hsrc', hkeeps', haw', henv'⟩ := hP
  exact ⟨S', hsteps, hdst', hN', hsrc', hkeeps', haw', henv'⟩

/-! ## The zero loop -/

/-- One round of `OUT[i] := 0`. -/
theorem mulZeroRound_steps [model : ExternalModel] {prog : List Asm}
    (l : MulModProcLabels) (n i : Nat)
    {k : List Asm} {σ : List AVal} {S : EvmState}
    (hZeroLoop : findLabel l.lZeroLoop prog =
      some (mulModZeroLoopBody l ++ k))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hi : i < n) (hn32 : n ≤ 32)
    (houtN : OUT + 32 * n ≤ Ncell)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = i)
    (houtL : yLimbs S.memory OUT n = List.replicate i 0 ++ (yLimbs S.memory OUT n).drop i) :
    ∃ S', ASteps prog ⟨mulModZeroLoopBody l ++ k, σ, S⟩
        ⟨mulModZeroLoopBody l ++ k, σ, S'⟩ ∧
      (loadWord S'.memory I2).toNat = i + 1 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      yLimbs S'.memory OUT n =
        List.replicate (i + 1) 0 ++ (yLimbs S.memory OUT n).drop (i + 1) ∧
      (∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < I2 ∨ I2 + 32 ≤ q) →
        S'.memory q = S.memory q) ∧
      S'.activeWords = S.activeWords ∧ S'.env = S.env := by
  have hi256 : i < 2 ^ 256 := by omega
  have hI2w : loadWord S.memory I2 = BitVec.ofNat 256 i := word_of_toNat hI2 hi256
  have hncellEq : Ncell = 0x1cc0 := rfl
  have houtEq : OUT = 0xc00 := rfl
  set S₁ : EvmState := {S with memory :=
      (storeWord S.memory (OUT + 32 * i) (BitVec.ofNat 256 0))} with hS₁def
  have hS₁mem : S₁.memory =
      storeWord S.memory (OUT + 32 * i) (BitVec.ofNat 256 0) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hI2₁ : (loadWord S₁.memory I2).toNat = i := by
    rw [hS₁mem, loadWord_storeWord_disj (p := OUT + 32 * i) (q := I2)
      (show OUT + 32 * i + 32 ≤ I2 ∨ I2 + 32 ≤ OUT + 32 * i by
        have := fragCells_ge I2 (by simp [fragCells]); omega)]
    exact hI2
  set S₂ : EvmState := {S₁ with memory :=
      (storeWord S₁.memory I2 (BitVec.ofNat 256 (i + 1)))} with hS₂def
  have hS₂mem : S₂.memory = storeWord S₁.memory I2 (BitVec.ofNat 256 (i + 1)) := rfl
  have hsteps : ASteps prog ⟨mulModZeroLoopBody l ++ k, σ, S⟩
      ⟨mulModZeroLoopBody l ++ k, σ, S₂⟩ := by
    rw [show mulModZeroLoopBody l =
        jumpUnlessLt (.load I2) (.load Ncell) l.lDone ++
        storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2))) (.imm 0) ++
        store I2 (.bin .add (.load I2) (.imm 1)) ++ [.jump l.lZeroLoop] from rfl]
    refine (exitTest_fall' (prog := prog) (l := l.lDone) haw hN hI2 (by omega) hi).trans ?_
    refine (storeAt_val (prog := prog)
      (addrE := .bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2)))
      (valE := .imm 0)
      (addr := OUT + 32 * i) (w := BitVec.ofNat 256 0)
      (eval_addr32 (base := OUT) (c := I2) hI2w)
      rfl
      (by omega)
      True.intro
      ⟨rfl, True.intro, ⟨rfl, True.intro,
        exprOK_load_cell' haw (by simp [fragCells])⟩⟩
      (by
        show OUT + 32 * i + 32 ≤ 32 * S.activeWords.toNat
        omega)).trans ?_
    refine (mulIncr_steps (prog := prog) (S := S₁) hawS₁ hI2₁).trans ?_
    exact ASteps.single (astep_jump hZeroLoop)
  refine ⟨S₂, hsteps, ?_, ?_, ?_, ?_, rfl, rfl⟩
  · rw [hS₂mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 256)]
  · have hNc : loadWord S₂.memory Ncell = loadWord S.memory Ncell := by
      rw [hS₂mem, hS₁mem]
      rw [loadWord_storeWord_disj (p := I2) (q := Ncell)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
        loadWord_storeWord_disj (p := OUT + 32 * i) (q := Ncell)
        (Or.inl (show OUT + 32 * i + 32 ≤ Ncell by omega))]
    rw [hNc]; exact hN
  · rw [hS₂mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₁mem,
      yLimbs_storeWord S.memory OUT n i hi (BitVec.ofNat 256 0),
      show (BitVec.ofNat 256 0).toNat = 0 from by
        rw [BitVec.toNat_ofNat, Nat.zero_mod],
      houtL,
      show (yLimbs S.memory OUT n).drop i =
          (yLimbs S.memory OUT n)[i]'(by
              rw [length_yLimbs S.memory OUT n]; omega) ::
            (yLimbs S.memory OUT n).drop (i + 1) from
        drop_cons_of_lt (yLimbs S.memory OUT n) i
          (by rw [length_yLimbs S.memory OUT n]; omega),
      show List.drop (i + 1)
          (List.replicate i 0 ++ (yLimbs S.memory OUT n)[i]'(by
              rw [length_yLimbs S.memory OUT n]; omega) ::
            List.drop (i + 1) (yLimbs S.memory OUT n))
          = List.drop (i + 1) (yLimbs S.memory OUT n) from by
        rw [List.drop_append, List.drop_replicate,
          show i + 1 - (List.replicate i 0).length = 1 from by simp,
          show i - (i + 1) = 0 from by omega]
        simp,
      set_append_mid'
        (show (List.replicate i 0).length = i from by simp),
      List.replicate_succ', List.append_assoc, List.cons_append]
    rfl
  · intro q hq1 hq2
    have hstep2 : S₂.memory q = S₁.memory q :=
      storeWord_other (p := I2) (a := q)
        (show q < I2 ∨ I2 + 32 ≤ q by omega)
    have hstep1 : S₁.memory q = S.memory q :=
      storeWord_other (p := OUT + 32 * i) (a := q)
        (show q < OUT + 32 * i ∨ OUT + 32 * i + 32 ≤ q by
          rcases hq1 with h | h
          · exact Or.inl (by omega)
          · exact Or.inr (by omega))
    rw [hstep2, hstep1]

/-- The full zero loop. -/
theorem mulZeroLoop_steps [model : ExternalModel] {prog : List Asm}
    (l : MulModProcLabels) (out₀ : List Nat) (n : Nat)
    {c' k : List Asm} {σ : List AVal} {S : EvmState}
    (hZeroLoop : findLabel l.lZeroLoop prog =
      some (mulModZeroLoopBody l ++ k))
    (hDone : findLabel l.lDone prog = some c')
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (houtN : OUT + 32 * n ≤ Ncell)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = 0)
    (houtL : yLimbs S.memory OUT n = out₀)
    (houtlen : out₀.length = n) :
    ∃ S', ASteps prog ⟨mulModZeroLoopBody l ++ k, σ, S⟩
        ⟨c', σ, S'⟩ ∧
      yLimbs S'.memory OUT n = List.replicate n 0 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      (∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < I2 ∨ I2 + 32 ≤ q) →
        S'.memory q = S.memory q) ∧
      S'.activeWords = S.activeWords ∧ S'.env = S.env := by
  obtain ⟨S', hP, hsteps⟩ :=
    loop_counted (model := model) (prog := prog)
      (top := mulModZeroLoopBody l ++ k) (σ := σ) (c' := c')
      (Inv := fun St m => ∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        yLimbs St.memory OUT n = List.replicate i 0 ++ out₀.drop i ∧
        (∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < I2 ∨ I2 + 32 ≤ q) →
          St.memory q = S.memory q) ∧
        St.activeWords = S.activeWords ∧ St.env = S.env)
      (P := fun St => yLimbs St.memory OUT n = List.replicate n 0 ∧
        (loadWord St.memory Ncell).toNat = n ∧
        (∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) → (q < I2 ∨ I2 + 32 ≤ q) →
          St.memory q = S.memory q) ∧
        St.activeWords = S.activeWords ∧ St.env = S.env)
      (fun {m St} _hmpos hm => by
        rcases hm with ⟨i, hI2i, him, hNst, houtst, hkeepst, hawEq, henvEq⟩
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exact absurd hm0 (by omega)
        · left
          have hin : i < n := by omega
          have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
            rw [hawEq]; exact haw
          obtain ⟨S', hsteps, hI2', hN', hout', hkeeps', hawEq', henvEq'⟩ :=
            mulZeroRound_steps (l := l) (n := n) (i := i) (k := k) hZeroLoop hawSt
              hin hn32 houtN hNst hI2i
              (by
                rw [houtst, List.drop_append, List.drop_replicate,
                  show i - (List.replicate i 0).length = 0 from by simp,
                  List.drop_drop, Nat.add_zero]
                simp)
          have hdropconv : (yLimbs St.memory OUT n).drop (i + 1) = out₀.drop (i + 1) := by
            rw [houtst, List.drop_append, List.drop_drop,
              show i + (i + 1 - (List.replicate i 0).length) = i + 1 from by simp]
            simp
          rw [hdropconv] at hout'
          have hawEq'' : S'.activeWords = S.activeWords := by rw [hawEq', hawEq]
          have hkeeps'' : ∀ q, (q < OUT ∨ OUT + 32 * n ≤ q) →
              (q < I2 ∨ I2 + 32 ≤ q) → S'.memory q = S.memory q :=
            fun q hq1 hq2 => (hkeeps' q hq1 hq2).trans (hkeepst q hq1 hq2)
          exact ⟨S', ⟨i + 1, hI2', by omega, hN', hout', hkeeps'',
            hawEq'', henvEq'.trans henvEq⟩, hsteps⟩)
      (fun St hm => by
        rcases hm with ⟨i, hI2i, him, hNst, houtst, hkeepst, hawEq, henvEq⟩
        have hI2n : i = n := by omega
        rw [hI2n, drop_eq_nil_of_length out₀ n (by omega), List.append_nil] at houtst
        refine ⟨⟨houtst, hNst, hkeepst, hawEq, henvEq⟩, ?_⟩
        rw [show mulModZeroLoopBody l =
            jumpUnlessLt (.load I2) (.load Ncell) l.lDone ++
            storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2))) (.imm 0) ++
            store I2 (.bin .add (.load I2) (.imm 1)) ++ [.jump l.lZeroLoop] from rfl]
        exact exitTest_taken' (model := model) (prog := prog) (l := l.lDone)
          (k := storeAt (.bin .add (.imm OUT) (.bin .mul (.imm 32) (.load I2))) (.imm 0) ++
            store I2 (.bin .add (.load I2) (.imm 1)) ++ [.jump l.lZeroLoop] ++ k)
          (by rw [hawEq]; exact haw) hNst hI2i (by omega) (by omega) hDone)
      (n := n) (yst := S)
      ⟨0, hI2, by omega, hN, by
        rw [List.replicate_zero, List.drop_zero]; exact houtL,
        fun _ _ _ => rfl, rfl, rfl⟩
  obtain ⟨hout', hN', hkeeps', haw', henv'⟩ := hP
  exact ⟨S', hsteps, hout', hN', hkeeps', haw', henv'⟩

/-! ## Value-level helpers for the scan and seeding -/

/-! ## Value-level helpers for the scan and seeding -/

theorem pow256_mul (h : Nat) : 2 ^ (256 * h) = radix ^ h := by
  rw [Nat.pow_mul, ← hradius]

/-- Word subtraction of one. -/
theorem ofNat_sub_one {h : Nat} (h1 : 1 ≤ h) (hlt : h < 2 ^ 256) :
    BitVec.ofNat 256 h - BitVec.ofNat 256 1 = BitVec.ofNat 256 (h - 1) := by
  apply BitVec.eq_of_toNat_eq
  have h2 := toNat_sub_eq (BitVec.ofNat 256 h) (BitVec.ofNat 256 1)
  have h3 : (BitVec.ofNat 256 h).toNat = h := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have h4 : (BitVec.ofNat 256 1).toNat = 1 := by decide
  have h5 : (BitVec.ofNat 256 (h - 1)).toNat = h - 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [h2, h3, h4, h5,
    show h + 2 ^ 256 - 1 = (h - 1) + 2 ^ 256 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (show h - 1 < 2 ^ 256 by omega)]

/-- The head entry of a cons. -/
theorem lget_cons_zero (x : Nat) (tl : List Nat) : lget (x :: tl) 0 = x := rfl

/-- The successor entry of a cons. -/
theorem lget_cons_succ (x : Nat) (tl : List Nat) (j : Nat) :
    lget (x :: tl) (j + 1) = lget tl j := by
  simp only [lget]
  have h0 : j + 1 = Nat.succ j := by omega
  rw [h0]
  rfl

/-- An all-zero limb list has value zero. -/
theorem ofDigits_zero_all : ∀ (L : List Nat), (∀ j, j < L.length → lget L j = 0) →
    Nat.ofDigits radix L = 0 := by
  intro L
  induction L with
  | nil => intro _; rfl
  | cons x tl ih =>
      intro h
      have hx : x = 0 := by
        have hz : lget (x :: tl) 0 = 0 := h 0 (by simp)
        rw [lget_cons_zero] at hz
        exact hz
      have htl : ∀ j, j < tl.length → lget tl j = 0 := by
        intro j hj
        rw [← lget_cons_succ x tl j]
        exact h (j + 1) (by simp only [List.length_cons]; omega)
      rw [Nat.ofDigits_cons, hx, ih htl]
      ring

/-- A list whose tail entries are all zero has value its head entry. -/
theorem ofDigits_head_zero_tail : ∀ (L : List Nat),
    (∀ j, 1 ≤ j → j < L.length → lget L j = 0) →
    Nat.ofDigits radix L = lget L 0 := by
  intro L
  cases L with
  | nil => intro _; rfl
  | cons x tl =>
      intro h
      have h0 : Nat.ofDigits radix tl = 0 := by
        apply ofDigits_zero_all
        intro j hj
        rw [← lget_cons_succ x tl j]
        exact h (j + 1) (by omega) (by simp only [List.length_cons]; omega)
      rw [Nat.ofDigits_cons, h0, Nat.mul_zero, Nat.add_zero, lget_cons_zero]

/-- `lget` through `drop`. -/
theorem lget_drop : ∀ (h : Nat) (bs : List Nat) (j : Nat),
    lget (bs.drop h) j = lget bs (h + j) := by
  intro h
  induction h with
  | zero => intro bs j; simp [List.drop_zero]
  | succ h ih =>
      intro bs j
      cases bs with
      | nil => simp [lget]
      | cons x tl =>
          simp only [List.drop_succ_cons, lget]
          have h0 : h + 1 + j = Nat.succ (h + j) := by omega
          rw [h0]
          have hr : (x :: tl).getD (Nat.succ (h + j)) 0 = tl.getD (h + j) 0 := rfl
          rw [hr]
          exact ih tl j

/-- Dividing a limb value by `radix ^ h` drops the low `h` limbs. -/
theorem div_ofDigits_drop : ∀ (h : Nat) (bs : List Nat), (∀ d ∈ bs, d < radix) →
    Nat.ofDigits radix bs / radix ^ h = Nat.ofDigits radix (bs.drop h) := by
  intro h
  induction h with
  | zero => intro bs _; simp
  | succ h ih =>
      intro bs hlt
      cases bs with
      | nil => simp
      | cons x tl =>
          have hx : x < radix := hlt x (by simp)
          have htl : ∀ d ∈ tl, d < radix := fun d hd => hlt d (by simp [hd])
          show (x + radix * Nat.ofDigits radix tl) / radix ^ (h + 1) =
            Nat.ofDigits radix (tl.drop h)
          rw [Nat.pow_succ, Nat.mul_comm (radix ^ h) radix,
            ← Nat.div_div_eq_div_mul _ radix (radix ^ h),
            Nat.add_mul_div_left _ _ radix_pos, Nat.div_eq_of_lt hx,
            Nat.zero_add]
          exact ih tl htl

/-- With every limb above `h` zero, `b / 2^(256h)` is exactly limb `h`. -/
theorem div_top_limb (bs : List Nat) (hlt : ∀ d ∈ bs, d < radix) (h : Nat)
    (hzero : ∀ j, h < j → j < bs.length → lget bs j = 0) (hlen : h < bs.length) :
    Nat.ofDigits radix bs / 2 ^ (256 * h) = lget bs h := by
  have hdlen : (bs.drop h).length = bs.length - h := List.length_drop
  have hside : ∀ j, 1 ≤ j → j < (bs.drop h).length → lget (bs.drop h) j = 0 := by
    intro j hj1 hj2
    rw [lget_drop h bs j, hzero (h + j) (by omega) (by omega)]
  rw [pow256_mul, div_ofDigits_drop h bs hlt,
    ofDigits_head_zero_tail (bs.drop h) hside, lget_drop_zero bs h hlen]

/-- A zero bit above the range certifies the value is below the smaller power. -/
theorem lt_pow_of_bit_zero {L m : Nat} (hL : L < 2 ^ (m + 1))
    (hb : (L / 2 ^ m) % 2 = 0) : L < 2 ^ m := by
  have hp : 0 < 2 ^ m := Nat.pow_pos (by omega)
  have hq : L / 2 ^ m < 2 := by
    rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm 2 (2 ^ m), ← Nat.pow_succ]
    exact hL
  have hq1 : L / 2 ^ m ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos (L / 2 ^ m) with h | h
  · have hdm : L = L % 2 ^ m := by
      have h2 := Nat.div_add_mod L (2 ^ m)
      rw [h, Nat.mul_zero, Nat.zero_add] at h2
      exact h2.symm
    rw [hdm]
    exact Nat.mod_lt L hp
  · have h1 : L / 2 ^ m = 1 := by omega
    rw [h1] at hb
    exact absurd hb (by decide)

/-- A set bit certifies the value reaches the smaller power. -/
theorem le_pow_of_bit_one {L m : Nat} (hb : (L / 2 ^ m) % 2 = 1) : 2 ^ m ≤ L := by
  have hp : 0 < 2 ^ m := Nat.pow_pos (by omega)
  refine (Nat.one_le_div_iff hp).1 ?_
  by_cases hz : L / 2 ^ m = 0
  · rw [hz] at hb
    exact absurd hb (by decide)
  · exact Nat.pos_of_ne_zero hz

/-- All-zero replicated limbs have value zero. -/
theorem ofDigits_replicate_zero : ∀ (n : Nat),
    Nat.ofDigits radix (List.replicate n 0) = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, Nat.ofDigits_cons, ih]
      ring

/-! ## Continuation suffixes at the procedure's labels -/

/-- The code from just after the top-bit body: copy-in, bits, and out. -/
def mulModAfterTopBit (l : MulModProcLabels) : List Asm :=
  [.label l.lCopy] ++ mulModCopyBody OUT ACC l.lBits l ++ [.label l.lBits] ++
  mulModBitsBody l ++ [.label l.lNextLimb] ++ mulModNextLimbBody l ++
  [.label l.lZero] ++ mulModZeroEntry ++ [.label l.lZeroLoop] ++ mulModZeroLoopBody l ++
  [.label l.lDone] ++ mulModRetEntry ++ [.label l.lRetCopy] ++ mulModRetCopyBody l ++
  [.label l.lExit] ++ [.dynJump]

theorem mulModFromTopBit_eq (l : MulModProcLabels) :
    mulModFromTopBit l =
      [.label l.lTopBit] ++ mulModTopBitBody l ++ mulModAfterTopBit l := by
  simp only [mulModFromTopBit, mulModAfterTopBit, List.append_assoc]

theorem mulModFromTopBit_eq2 (l : MulModProcLabels) (k : List Asm) :
    mulModFromTopBit l ++ k =
    [.label l.lTopBit] ++ (mulModTopBitBody l ++ ([.label l.lCopy] ++
      (mulModCopyBody OUT ACC l.lBits l ++ ([.label l.lBits] ++
        (mulModFromBits l ++ k))))) := by
  simp only [mulModFromTopBit, mulModFromBits, List.append_assoc]

/-- The suffix from the `lNextLimb` label onward, as one block. -/
def mulModBitsTail (l : MulModProcLabels) : List Asm :=
  [.label l.lNextLimb] ++ mulModFromNextLimb l

theorem mulModFromBits_eq2 (l : MulModProcLabels) (k : List Asm) :
    mulModFromBits l ++ k =
      mulModBitsBody l ++ (mulModBitsTail l ++ k) := by
  simp only [mulModFromBits, mulModBitsTail, mulModFromNextLimb,
    List.append_assoc]

theorem mulModBitsTail_eq (l : MulModProcLabels) (k : List Asm) :
    mulModBitsTail l ++ k =
      [.label l.lNextLimb] ++
        (mulModNextLimbBody l ++
          ([.label l.lZero] ++ (mulModFromZero l ++ k))) := by
  simp only [mulModBitsTail, mulModFromNextLimb, mulModFromZero,
    List.append_assoc]

theorem mulModFromNextLimb_eq2 (l : MulModProcLabels) (k : List Asm) :
    mulModFromNextLimb l ++ k =
      mulModNextLimbBody l ++
        ([.label l.lZero] ++ (mulModFromZero l ++ k)) := by
  simp only [mulModFromNextLimb, mulModFromZero, List.append_assoc]

theorem mulModFromZero_eq (l : MulModProcLabels) (k : List Asm) :
    mulModFromZero l ++ k =
      mulModZeroEntry ++
        ([.label l.lZeroLoop] ++
          (mulModZeroLoopBody l ++
            ([.label l.lDone] ++ (mulModFromRet l ++ k)))) := by
  simp only [mulModFromZero, mulModFromRet, mulModZeroEntry, mulModRetEntry,
    List.append_assoc]

/-- The right-nested body spellings used by per-piece step chaining. -/
theorem mulModScanTopBody_eq (l : MulModProcLabels) (k : List Asm) :
    mulModScanTopBody l ++ k =
      jumpIfZ (.load HIcell) l.lZero ++
      (store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
      (jumpIfZ (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell))))
        l.lScanTop ++
      (store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
      (store T1 (.imm 256) ++ k)))) := by
  simp only [mulModScanTopBody, List.append_assoc]

theorem mulModTopBitBody_eq (l : MulModProcLabels) (k : List Asm) :
    mulModTopBitBody l ++ k =
      store T1 (.bin .sub (.load T1) (.imm 1)) ++
      (jumpIfZ (bitTestOf T0 T1) l.lTopBit ++ (store I2 (.imm 0) ++ k)) := by
  simp only [mulModTopBitBody, List.append_assoc]

theorem mulModBitsBody_eq (l : MulModProcLabels) (k : List Asm) :
    mulModBitsBody l ++ k =
      jumpIfZ (.load T1) l.lNextLimb ++
      (store T1 (.bin .sub (.load T1) (.imm 1)) ++
      (mmCallSite OUT OUT l.lSqRet l.lamEntry ++
      (jumpIfZ (bitTestOf T0 T1) l.lBits ++
      (mmCallSite OUT ACC l.lAddRet l.lamEntry ++ ([.jump l.lBits] ++ k))))) := by
  simp only [mulModBitsBody, mmCallSite, List.append_assoc]

theorem mulModNextLimbBody_eq (l : MulModProcLabels) (k : List Asm) :
    mulModNextLimbBody l ++ k =
      jumpIfZ (.load HIcell) l.lDone ++
      (store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
      (store T1 (.imm 256) ++
      (store T0 (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell)))) ++
      ([.jump l.lBits] ++ k)))) := by
  simp only [mulModNextLimbBody, List.append_assoc]

/-- The complete `lBits` suffix in one right-associated normal form. -/
theorem mulModBitsTop_eq (l : MulModProcLabels) (k : List Asm) :
    mulModFromBits l ++ k =
      jumpIfZ (.load T1) l.lNextLimb ++
      store T1 (.bin .sub (.load T1) (.imm 1)) ++
      mmCallSite OUT OUT l.lSqRet l.lamEntry ++
      jumpIfZ (bitTestOf T0 T1) l.lBits ++
      mmCallSite OUT ACC l.lAddRet l.lamEntry ++
      [.jump l.lBits] ++
      [.label l.lNextLimb] ++
      jumpIfZ (.load HIcell) l.lDone ++
      store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
      store T1 (.imm 256) ++
      store T0 (loadAt (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell)))) ++
      [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ k := by
  simp only [mulModFromBits, mulModBitsBody, mmCallSite, mulModNextLimbBody,
    mulModFromZero, mulModZeroEntry, mulModRetEntry, List.append_assoc]

/-- Reading a non-addMod-scratch cell through an addMod frame. -/
theorem loadWord_of_addKeeps {M M₀ : Nat → UInt8} {n q : Nat}
    (h : AddModKeeps M M₀ OUT n)
    (h1 : q + 32 ≤ OUT ∨ OUT + 32 * n ≤ q)
    (h3 : q + 32 ≤ SUBC ∨ SUBC + 32 * n ≤ q)
    (h4 : ∀ c ∈ addModScratch, q + 32 ≤ c ∨ c + 32 ≤ q) :
    loadWord M q = loadWord M₀ q := by
  rw [loadWord_congr]
  intro a ha1 ha2
  exact h a (by rcases h1 with h | h <;> omega)
    (by rcases h3 with h | h <;> omega)
    (fun c hc => by rcases h4 c hc with h | h <;> omega)

/-- The register cells sit in disjoint windows from the addMod scratch cells. -/
theorem addScratch_vs_regs : ∀ c ∈ addModScratch,
    ∀ d ∈ [(Ncell : Nat), HIcell, BPTR, T0, T1], d + 32 ≤ c ∨ c + 32 ≤ d := by
  decide

/-- The limb decomposition used by every bit round. -/
theorem div_decomp (bs : List Nat) (hlt : ∀ d ∈ bs, d < radix) (b : Nat)
    (hbv : b = Nat.ofDigits radix bs) (h : Nat) :
    b / 2 ^ (256 * h) = lget bs h + 2 ^ 256 * (b / 2 ^ (256 * (h + 1))) := by
  have hdiv1 : b / 2 ^ (256 * h) / 2 ^ 256 = b / 2 ^ (256 * (h + 1)) := by
    rw [Nat.div_div_eq_div_mul b (2 ^ (256 * h)) (2 ^ 256),
      show 2 ^ (256 * h) * 2 ^ 256 = 2 ^ (256 * (h + 1)) from by
        rw [← Nat.pow_add, Nat.mul_add, Nat.mul_one]]
  have hmod1 : b / 2 ^ (256 * h) % 2 ^ 256 = lget bs h := by
    rw [hbv]
    exact div_limb bs hlt h
  have h2 := Nat.div_add_mod (b / 2 ^ (256 * h)) (2 ^ 256)
  rw [hdiv1, hmod1] at h2
  omega

set_option maxHeartbeats 80000000 in
/-- The scan loop: from `HI = h` with every limb at or above `h` zero, either
all limbs are zero (exit to the zeroing path, left) or the loop finds the top
nonzero limb `h* < h`, loading it into `T0` with `T1 = 256` and `HI = h*`
(right, entering the top-bit phase). -/
theorem mulScan_steps [model : ExternalModel] {prog : List Asm}
    (bptr : Nat) (l : MulModProcLabels) (bs : List Nat) (n : Nat)
    {cont : List Asm} {σ : List AVal} {M₀ : Nat → UInt8}
    (hScan : findLabel l.lScanTop prog =
      some (mulModScanTopBody l ++ mulModFromTopBit l ++ cont))
    (hZero : findLabel l.lZero prog = some (mulModFromZero l ++ cont))
    (hn : 0 < n) (hn32 : n ≤ 32) (hbptrN : bptr + 32 * n ≤ Ncell) :
    ∀ (h : Nat) (S : EvmState),
      0x1f40 ≤ 32 * S.activeWords.toNat →
      (loadWord S.memory Ncell).toNat = n →
      MulModKeeps S.memory M₀ n →
      yLimbs S.memory bptr n = bs →
      (loadWord S.memory BPTR).toNat = bptr →
      (loadWord S.memory HIcell).toNat = h →
      h ≤ n → (∀ j, h ≤ j → j < n → lget bs j = 0) →
      (∃ S', ASteps prog
          ⟨mulModScanTopBody l ++ mulModFromTopBit l ++ cont, σ, S⟩
          ⟨mulModFromZero l ++ cont, σ, S'⟩ ∧
        (∀ j, j < n → lget bs j = 0) ∧
        MulModKeeps S'.memory M₀ n ∧ (loadWord S'.memory Ncell).toNat = n ∧
        S'.activeWords = S.activeWords ∧ yLimbs S'.memory bptr n = bs ∧
        S'.env = S.env)
      ∨ (∃ S', ASteps prog
          ⟨mulModScanTopBody l ++ mulModFromTopBit l ++ cont, σ, S⟩
          ⟨mulModFromTopBit l ++ cont, σ, S'⟩ ∧
        ∃ h', h' < n ∧ lget bs h' ≠ 0 ∧
          (loadWord S'.memory HIcell).toNat = h' ∧
          (loadWord S'.memory T0).toNat = lget bs h' ∧
          (loadWord S'.memory T1).toNat = 256 ∧
          (∀ j, h' < j → j < n → lget bs j = 0) ∧
          MulModKeeps S'.memory M₀ n ∧ (loadWord S'.memory Ncell).toNat = n ∧
          S'.activeWords = S.activeWords ∧ yLimbs S'.memory bptr n = bs ∧
          yLimbs S'.memory ACC n = yLimbs S.memory ACC n ∧
          S'.env = S.env) := by
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hHIlit : (HIcell : Nat) = 0x1d80 := rfl
  have hT0lit : (T0 : Nat) = 0x1dc0 := rfl
  have hT1lit : (T1 : Nat) = 0x1de0 := rfl
  have hI2lit : (I2 : Nat) = 0x1e60 := rfl
  intro h
  induction h with
  | zero =>
      intro S haw hN hkeeps hbs hBPTR hHI hle hupper
      have hHIw : loadWord S.memory HIcell = 0 :=
        word_of_toNat hHI (by decide)
      left
      refine ⟨S, ?_, fun j hj => hupper j (by omega) hj, hkeeps, hN, rfl, hbs, rfl⟩
      rw [mulModScanTopBody_eq]
      exact jumpIfZ_taken (e := .load HIcell) (l := l.lZero)
        (c' := mulModFromZero l ++ cont)
        (k := store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
          (jumpIfZ (loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell))))
            l.lScanTop ++
          (store T0 (loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) ++
          (store T1 (.imm 256) ++
            (mulModFromTopBit l ++ cont)))))
        (exprOK_load_cell' haw (by simp [fragCells]))
        (by
            show loadWord S.memory HIcell = 0
            exact hHIw)
        hZero
  | succ h ih =>
      intro S haw hN hkeeps hbs hBPTR hHI hle hupper
      have hlt256 : h + 1 < 2 ^ 256 := by omega
      have hHIw : loadWord S.memory HIcell = BitVec.ofNat 256 (h + 1) :=
        word_of_toNat hHI hlt256
      -- step 1: HI = 0 test falls through (h + 1 ≠ 0)
      have s1 : ASteps prog
          ⟨jumpIfZ (.load HIcell) l.lZero ++
            (store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
            (jumpIfZ (loadAt (.bin .add (.load BPTR)
              (.bin .mul (.imm 32) (.load HIcell)))) l.lScanTop ++
            (store T0 (loadAt (.bin .add (.load BPTR)
              (.bin .mul (.imm 32) (.load HIcell)))) ++
            (store T1 (.imm 256) ++
              (mulModFromTopBit l ++ cont))))), σ, S⟩
          ⟨store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
            (jumpIfZ (loadAt (.bin .add (.load BPTR)
              (.bin .mul (.imm 32) (.load HIcell)))) l.lScanTop ++
            (store T0 (loadAt (.bin .add (.load BPTR)
              (.bin .mul (.imm 32) (.load HIcell)))) ++
            (store T1 (.imm 256) ++
              (mulModFromTopBit l ++ cont)))), σ, S⟩ :=
        jumpIfZ_fall (e := .load HIcell) (l := l.lZero)
          (exprOK_load_cell' haw (by simp [fragCells]))
          (by
            show loadWord S.memory HIcell ≠ 0
            rw [hHIw]
            exact ofNat_ne_zero hlt256 (by omega))
      -- step 2: HI := h
      have hev2 : evalExpr (.bin .sub (.load HIcell) (.imm 1)) S
          = BitVec.ofNat 256 h := by
        show loadWord S.memory HIcell - BitVec.ofNat 256 1 = BitVec.ofNat 256 h
        rw [hHIw, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
      have s2 := store_cell_val (prog := prog) (c := HIcell)
        (e := .bin .sub (.load HIcell) (.imm 1)) (w := BitVec.ofNat 256 h)
        (k := jumpIfZ (loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) l.lScanTop ++
          (store T0 (loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) ++
          (store T1 (.imm 256) ++
            (mulModFromTopBit l ++ cont))))
        (σ := σ) hev2
        ⟨rfl, exprOK_load_cell' haw (by simp [fragCells]), True.intro⟩
        (haw_pin haw (by simp [fragCells]))
      -- S₁ = S with HI := h
      set S₁ : EvmState := {S with memory :=
          (storeWord S.memory HIcell (BitVec.ofNat 256 h))} with hS₁def
      have hS₁mem : S₁.memory =
          storeWord S.memory HIcell (BitVec.ofNat 256 h) := rfl
      have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
      have hh256 : h < 2 ^ 256 := by omega
      have hHI₁ : (loadWord S₁.memory HIcell).toNat = h := by
        rw [hS₁mem, loadWord_storeWord, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hh256]
      have hHIw₁ : loadWord S₁.memory HIcell = BitVec.ofNat 256 h :=
        word_of_toNat hHI₁ hh256
      have hN₁ : (loadWord S₁.memory Ncell).toNat = n := by
        rw [hS₁mem, loadWord_storeWord_disj (p := HIcell) (q := Ncell)
          (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
        exact hN
      have hkeeps₁ : MulModKeeps S₁.memory M₀ n :=
        mulKeeps_storeWord hkeeps
          (Or.inr (by simp [mulModScratch]))
      have hbs₁ : yLimbs S₁.memory bptr n = bs := by
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := HIcell)
          (Or.inr (by omega))]
        exact hbs
      have hbslen : bs.length = n := by
        rw [← hbs]; exact length_yLimbs S.memory bptr n
      have hlimb : (loadWord S₁.memory (bptr + 32 * h)).toNat = lget bs h :=
        yLimb_lget (show h < n by omega) hbs₁ (by omega)
      -- step 3: the limb test
      have haddr1 : bptr + 32 * h < 2 ^ 256 := by omega
      have hBPTRw₁ : loadWord S₁.memory BPTR = BitVec.ofNat 256 bptr := by
        rw [hS₁mem, loadWord_storeWord_disj (p := HIcell) (q := BPTR)
          (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
        exact BPTR_word hBPTR (by omega)
      have s3val : evalExpr (loadAt (.bin .add (.load BPTR)
          (.bin .mul (.imm 32) (.load HIcell)))) S₁ =
          loadWord S₁.memory (bptr + 32 * h) :=
        eval_loadAt_bptr hBPTRw₁ hHIw₁ haddr1
      have s3ok : exprOK (loadAt (.bin .add (.load BPTR)
          (.bin .mul (.imm 32) (.load HIcell)))) S₁ := by
        refine ⟨?_, rfl, exprOK_load_cell' hawS₁ (by simp [fragCells]), rfl,
          True.intro, exprOK_load_cell' hawS₁ (by simp [fragCells])⟩
        show (evalExpr (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell))) S₁).toNat + 32 ≤
          32 * S₁.activeWords.toNat
        rw [eval_addr_bptr hBPTRw₁ hHIw₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr1]
        omega
      rcases Nat.eq_zero_or_pos (lget bs h) with hlimb0 | hlimbp
      · -- zero limb: jump back to the scan top and recurse
        have hword0 : evalExpr (loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) S₁ = 0 := by
          rw [s3val]
          have : loadWord S₁.memory (bptr + 32 * h)
              = BitVec.ofNat 256 (lget bs h) := word_of_toNat hlimb (by omega)
          rw [this, hlimb0]
          rfl
        have s3 := jumpIfZ_taken (σ := σ) (e := loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) (l := l.lScanTop)
          (c' := mulModScanTopBody l ++
            (mulModFromTopBit l ++ cont))
          (k := store T0 (loadAt (.bin .add (.load BPTR)
              (.bin .mul (.imm 32) (.load HIcell)))) ++
            (store T1 (.imm 256) ++
              (mulModFromTopBit l ++ cont)))
          s3ok hword0 hScan
        have hupper' : ∀ j, h ≤ j → j < n → lget bs j = 0 := by
          intro j hj1 hj2
          rcases Nat.lt_or_ge j (h + 1) with hj | hj
          · have hj' : j = h := by omega
            rw [hj']
            exact hlimb0
          · exact hupper j (by omega) hj2
        have hBPTR₁ : (loadWord S₁.memory BPTR).toNat = bptr := by
          rw [hBPTRw₁, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        exact (ih S₁ hawS₁ hN₁ hkeeps₁ hbs₁ hBPTR₁ hHI₁ (by omega) hupper').imp
          (fun ⟨S', hs, hzerolimbs, hkeeps', hN', haw', hbs', henv'⟩ =>
            ⟨S', ((s1.trans s2).trans s3).trans hs, hzerolimbs, hkeeps', hN',
              by rw [haw'], hbs', henv'.trans rfl⟩)
          (fun ⟨S', hs, h', hh'ltn, hh'ne, hHI', hT0', hT1', hupper', hkeeps',
            hN', haw', hbs', hacc', henv'⟩ =>
            ⟨S', ((s1.trans s2).trans s3).trans hs, h', hh'ltn, hh'ne, hHI',
              hT0', hT1', hupper', hkeeps', hN', by rw [haw'], hbs',
              hacc'.trans (by
                rw [hS₁mem, yLimbs_storeWord_disjoint (q := HIcell)
                 (Or.inr (by omega))]), henv'.trans rfl⟩)
      · -- nonzero limb: load T0 and T1, fall through to the top-bit phase
        have hwordne : evalExpr (loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) S₁ ≠ 0 := by
          rw [s3val]
          have hw : loadWord S₁.memory (bptr + 32 * h)
              = BitVec.ofNat 256 (lget bs h) := word_of_toNat hlimb (by omega)
          rw [hw]
          exact ofNat_ne_zero (by omega) (by omega)
        have s3 := jumpIfZ_fall (prog := prog) (σ := σ)
           (e := loadAt (.bin .add (.load BPTR)
            (.bin .mul (.imm 32) (.load HIcell)))) (l := l.lScanTop)
          (k := store T0 (loadAt (.bin .add (.load BPTR)
              (.bin .mul (.imm 32) (.load HIcell)))) ++
            (store T1 (.imm 256) ++
              (mulModFromTopBit l ++ cont)))
          s3ok hwordne
        have s4 := store_cell_val (prog := prog) (c := T0)
          (e := loadAt (.bin .add (.load BPTR) (.bin .mul (.imm 32) (.load HIcell))))
          (w := loadWord S₁.memory (bptr + 32 * h))
          (k := store T1 (.imm 256) ++
            (mulModFromTopBit l ++ cont))
          (σ := σ) (yst := S₁) s3val
          ⟨s3ok.1, s3ok.2⟩
          (haw_pin hawS₁ (by simp [fragCells]))
        set S₂ : EvmState := {S₁ with memory :=
            (storeWord S₁.memory T0 (loadWord S₁.memory (bptr + 32 * h)))} with hS₂def
        have hS₂mem : S₂.memory =
            storeWord S₁.memory T0 (loadWord S₁.memory (bptr + 32 * h)) := rfl
        have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := hawS₁
        have s5 := store_cell_val (prog := prog) (c := T1) (e := .imm 256)
          (w := BitVec.ofNat 256 256)
          (k := mulModFromTopBit l ++ cont)
          (σ := σ) (yst := S₂) rfl True.intro
          (haw_pin hawS₂ (by simp [fragCells]))
        set S₃ : EvmState := {S₂ with memory :=
            (storeWord S₂.memory T1 (BitVec.ofNat 256 256))} with hS₃def
        have hS₃mem : S₃.memory =
            storeWord S₂.memory T1 (BitVec.ofNat 256 256) := rfl
        -- state facts
        have hHI₃ : (loadWord S₃.memory HIcell).toNat = h := by
          rw [hS₃mem, loadWord_storeWord_disj (p := T1) (q := HIcell)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
            hS₂mem, loadWord_storeWord_disj (p := T0) (q := HIcell)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
          exact hHI₁
        have hT0₃ : (loadWord S₃.memory T0).toNat = lget bs h := by
          rw [hS₃mem, loadWord_storeWord_disj (p := T1) (q := T0)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
            hS₂mem, loadWord_storeWord, hlimb]
        have hT1₃ : (loadWord S₃.memory T1).toNat = 256 := by
          rw [hS₃mem, loadWord_storeWord, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt (by decide : (256 : Nat) < 2 ^ 256)]
        have hN₃ : (loadWord S₃.memory Ncell).toNat = n := by
          rw [hS₃mem, loadWord_storeWord_disj (p := T1) (q := Ncell)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
            hS₂mem, loadWord_storeWord_disj (p := T0) (q := Ncell)
            (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
          exact hN₁
        have hkeeps₃ : MulModKeeps S₃.memory M₀ n :=
          mulKeeps_storeWord (mulKeeps_storeWord hkeeps₁
            (Or.inr (by simp [mulModScratch])))
            (Or.inr (by simp [mulModScratch]))
        have hbs₃ : yLimbs S₃.memory bptr n = bs := by
          rw [hS₃mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega)),
            hS₂mem, yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega))]
          exact hbs₁
        have hacc₃ : yLimbs S₃.memory ACC n = yLimbs S.memory ACC n := by
          rw [hS₃mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega)),
            hS₂mem, yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega)),
            hS₁mem, yLimbs_storeWord_disjoint (q := HIcell) (Or.inr (by omega))]
        have hsteps : ASteps prog
            ⟨mulModScanTopBody l ++ mulModFromTopBit l ++ cont, σ, S⟩
            ⟨mulModFromTopBit l ++ cont, σ, S₃⟩ := by
          rw [mulModScanTopBody_eq]
          exact ((((s1.trans s2).trans s3).trans s4).trans s5)
        right
        exact ⟨S₃, hsteps, h, by omega, by omega, hHI₃, hT0₃, hT1₃,
          fun j hj1 hj2 => hupper j (by omega) hj2, hkeeps₃, hN₃, rfl, hbs₃,
          hacc₃, rfl⟩

/-! ## The top-bit loop -/
theorem mulTopBit_steps [model : ExternalModel] {prog : List Asm}
    (l : MulModProcLabels) (n h L : Nat) {k : List Asm} {σ : List AVal}
    {S : EvmState} {M₀ : Nat → UInt8}
    (hTopBit : findLabel l.lTopBit prog =
      some (mulModTopBitBody l ++ [.label l.lCopy] ++ k))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat) (hn32 : n ≤ 32)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hHI : (loadWord S.memory HIcell).toNat = h)
    (hT1 : (loadWord S.memory T1).toNat = 256)
    (hT0 : (loadWord S.memory T0).toNat = L) (hL0 : 0 < L) (hL256 : L < 2 ^ 256)
    (hkeeps : MulModKeeps S.memory M₀ n) :
    ∃ S' τ, ASteps prog ⟨mulModTopBitBody l ++ [.label l.lCopy] ++ k, σ, S⟩
        ⟨k, σ, S'⟩ ∧
      (loadWord S'.memory T1).toNat = τ ∧ 2 ^ τ ≤ L ∧ L < 2 ^ (τ + 1) ∧
      (loadWord S'.memory HIcell).toNat = h ∧
      (loadWord S'.memory T0).toNat = L ∧
      (loadWord S'.memory I2).toNat = 0 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      yLimbs S'.memory ACC n = yLimbs S.memory ACC n ∧
      MulModKeeps S'.memory M₀ n ∧ S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  -- the exit path: fall through the bit test, `I2 := 0`, step `l.lCopy`
  have hexitpath : ∀ (St : EvmState), 0x1f40 ≤ 32 * St.activeWords.toNat →
      ASteps prog ⟨store I2 (.imm 0) ++ ([.label l.lCopy] ++ k), σ, St⟩
        ⟨k, σ,
          {St with memory := (storeWord St.memory I2 (BitVec.ofNat 256 0))}⟩ := by
    intro St hawSt
    have h0 := store_cell_val (prog := prog) (c := I2) (e := .imm 0)
      (w := BitVec.ofNat 256 0) (k := [.label l.lCopy] ++ k) (σ := σ)
      (yst := St) rfl True.intro
      (haw_pin hawSt (by simp [fragCells]))
    exact h0.trans (ASteps.single (astep_label (prog := prog) (l := l.lCopy)
      (k := k) (σ := σ)
      (yst := {St with memory :=
        (storeWord St.memory I2 (BitVec.ofNat 256 0))})))
  -- the main countdown, from T1 = t (1 ≤ t ≤ 256, L < 2 ^ t)
  have main : ∀ (t : Nat) (St : EvmState),
      0x1f40 ≤ 32 * St.activeWords.toNat →
      (loadWord St.memory Ncell).toNat = n →
      (loadWord St.memory HIcell).toNat = h →
      (loadWord St.memory T1).toNat = t →
      (loadWord St.memory T0).toNat = L →
      0 < L ∧ L < 2 ^ t → t ≤ 256 →
      MulModKeeps St.memory M₀ n →
      ∃ S' τ, ASteps prog
          ⟨mulModTopBitBody l ++ [.label l.lCopy] ++ k, σ, St⟩ ⟨k, σ, S'⟩ ∧
        (loadWord S'.memory T1).toNat = τ ∧ 2 ^ τ ≤ L ∧ L < 2 ^ (τ + 1) ∧
        (loadWord S'.memory HIcell).toNat = h ∧
        (loadWord S'.memory T0).toNat = L ∧
        (loadWord S'.memory I2).toNat = 0 ∧
        (loadWord S'.memory Ncell).toNat = n ∧
        yLimbs S'.memory ACC n = yLimbs St.memory ACC n ∧
        MulModKeeps S'.memory M₀ n ∧ S'.activeWords = St.activeWords ∧
        S'.env = St.env := by
    intro t
    induction t with
    | zero => intro St _hawSt _ _ hT1t _ hLpos _ _
              exact absurd hLpos (by rw [Nat.pow_zero] at hLpos; omega)
    | succ t ih =>
      intro St hawSt hNst hHIst hT1t hT0st hLpos hLt hkeepsst
      have ht256 : t < 2 ^ 256 := by omega
      have hT1w : loadWord St.memory T1 = BitVec.ofNat 256 (t + 1) :=
        word_of_toNat hT1t (by omega)
      -- T1 := t
      have hev : evalExpr (.bin .sub (.load T1) (.imm 1)) St
          = BitVec.ofNat 256 t := by
        show loadWord St.memory T1 - BitVec.ofNat 256 1 = BitVec.ofNat 256 t
        rw [hT1w, ofNat_sub_one (by omega) (by omega), Nat.add_sub_cancel]
      have s1 := store_cell_val (prog := prog) (c := T1)
        (e := .bin .sub (.load T1) (.imm 1)) (w := BitVec.ofNat 256 t)
        (k := jumpIfZ (bitTestOf T0 T1) l.lTopBit ++
          (store I2 (.imm 0) ++ ([.label l.lCopy] ++ k)))
        (σ := σ) hev ⟨rfl, exprOK_load_cell' hawSt (by simp [fragCells]),
          True.intro⟩
        (haw_pin hawSt (by simp [fragCells]))
      set S₁ : EvmState := {St with memory :=
          (storeWord St.memory T1 (BitVec.ofNat 256 t))} with hS₁def
      have hS₁mem : S₁.memory =
          storeWord St.memory T1 (BitVec.ofNat 256 t) := rfl
      have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := hawSt
      have hT0₁ : (loadWord S₁.memory T0).toNat = L := by
        rw [hS₁mem, loadWord_storeWord_disj (p := T1) (q := T0)
          (cells_disj (by simp [fragCells]) (by simp [fragCells])
            (by decide))]
        exact hT0st
      have hT1₁ : (loadWord S₁.memory T1).toNat = t := by
        rw [hS₁mem, loadWord_storeWord, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ht256]
      have hT1w₁ : loadWord S₁.memory T1 = BitVec.ofNat 256 t :=
        word_of_toNat hT1₁ ht256
      have hT0w₁ : loadWord S₁.memory T0 = BitVec.ofNat 256 L :=
        word_of_toNat hT0₁ hL256
      have hbit : (evalExpr (bitTestOf T0 T1) S₁).toNat = L / 2 ^ t % 2 := by
        rw [toNat_bitTestOf hT0w₁ hT1w₁ (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hL256]
      have hbitok : exprOK (bitTestOf T0 T1) S₁ :=
        ⟨rfl, ⟨rfl, exprOK_load_cell' hawS₁ (by simp [fragCells]),
          exprOK_load_cell' hawS₁ (by simp [fragCells])⟩, True.intro⟩
      have hword : evalExpr (bitTestOf T0 T1) S₁
          = BitVec.ofNat 256 (L / 2 ^ t % 2) :=
        word_of_toNat (by rw [hbit]) (by omega)
      have hHI₁ : (loadWord S₁.memory HIcell).toNat = h := by
        rw [hS₁mem, loadWord_storeWord_disj (p := T1) (q := HIcell)
          (cells_disj (by simp [fragCells]) (by simp [fragCells])
            (by decide))]
        exact hHIst
      have hN₁ : (loadWord S₁.memory Ncell).toNat = n := by
        rw [hS₁mem, loadWord_storeWord_disj (p := T1) (q := Ncell)
          (cells_disj (by simp [fragCells]) (by simp [fragCells])
            (by decide))]
        exact hNst
      have hkeeps₁ : MulModKeeps S₁.memory M₀ n :=
        mulKeeps_storeWord hkeepsst (Or.inr (by simp [mulModScratch]))
      have haccst : yLimbs S₁.memory ACC n = yLimbs St.memory ACC n := by
        rw [hS₁mem, yLimbs_storeWord_disjoint (q := T1)
          (Or.inr (by
            have hA : (ACC : Nat) = 0x800 := rfl
            have hT : (T1 : Nat) = 0x1de0 := rfl
            omega))]
      rcases Nat.eq_zero_or_pos (L / 2 ^ t % 2) with hb0 | hbp
      · -- bit zero: loop back with T1 = t and a smaller range
        have hsteps : ASteps prog
            ⟨mulModTopBitBody l ++ [.label l.lCopy] ++ k, σ, St⟩
            ⟨mulModTopBitBody l ++ [.label l.lCopy] ++ k, σ, S₁⟩ := by
          rw [mulModTopBitBody_eq]
          exact (s1.trans (jumpIfZ_taken (e := bitTestOf T0 T1)
            (l := l.lTopBit)
            (c' := mulModTopBitBody l ++ ([.label l.lCopy] ++ k))
            (k := store I2 (.imm 0) ++ ([.label l.lCopy] ++ k))
            hbitok (by rw [hword, hb0]; rfl) hTopBit))
        have hLtpos : 0 < L ∧ L < 2 ^ t :=
          ⟨hLpos.1, lt_pow_of_bit_zero hLpos.2 hb0⟩
        obtain ⟨S₂, τ, hrest, hT1₂, hle, hltτ, hHI₂, hT0₂, hI2₂, hN₂,
          hacc₂, hkeeps₂, haw₂, henv₂⟩ :=
          ih S₁ hawS₁ hN₁ hHI₁ hT1₁ hT0₁ hLtpos (by omega) hkeeps₁
        exact ⟨S₂, τ, hsteps.trans hrest, hT1₂, hle, hltτ, hHI₂, hT0₂,
          hI2₂, hN₂, hacc₂.trans haccst, hkeeps₂, by rw [haw₂],
          henv₂.trans rfl⟩
      · -- bit set: exit with τ = t
        have hb1 : L / 2 ^ t % 2 = 1 := by
          have hmod := Nat.mod_lt (L / 2 ^ t) (show (0 : Nat) < 2 by omega)
          omega
        have hfin := hexitpath S₁ hawS₁
        have hI2zero : (loadWord (storeWord S₁.memory I2 (BitVec.ofNat 256 0))
            I2).toNat = 0 := by
          rw [loadWord_storeWord, BitVec.toNat_ofNat]
        have hkeeps' : MulModKeeps
            (storeWord S₁.memory I2 (BitVec.ofNat 256 0)) M₀ n :=
          mulKeeps_storeWord hkeeps₁
            (Or.inr (Or.inr (Or.inr (mulScratch_add
              (show I2 ∈ addModScratch by decide)))))
        have haccst' : yLimbs (storeWord S₁.memory I2 (BitVec.ofNat 256 0))
            ACC n = yLimbs St.memory ACC n := by
          rw [yLimbs_storeWord_disjoint (q := I2)
            (Or.inr (by
              have hA : (ACC : Nat) = 0x800 := rfl
              have hI : (I2 : Nat) = 0x1e60 := rfl
              omega))]
          exact haccst
        refine ⟨{S₁ with memory :=
            (storeWord S₁.memory I2 (BitVec.ofNat 256 0))}, t, ?_, hT1₁,
          le_pow_of_bit_one hb1, hLpos.2, hHI₁, hT0₁, hI2zero, hN₁, haccst',
          hkeeps', rfl, rfl⟩
        rw [mulModTopBitBody_eq]
        exact (s1.trans (jumpIfZ_fall (e := bitTestOf T0 T1)
          (l := l.lTopBit)
          (k := store I2 (.imm 0) ++ ([.label l.lCopy] ++ k))
          hbitok (by
            rw [hword, hb1]
            decide))).trans hfin
  exact main 256 S haw hN hHI hT1 hT0 ⟨hL0, hL256⟩ (by omega) hkeeps

/-! ## The `T1 = 0` limb transition round -/
theorem mulBitsT0Round_steps [model : ExternalModel] {prog : List Asm}
    (bptr : Nat) (l : MulModProcLabels)
    (bs : List Nat) (n m a b h : Nat)
    {cont : List Asm} {σ : List AVal} {St : EvmState} {M₀ : Nat → UInt8}
    (hBits : findLabel l.lBits prog =
      some (mulModFromBits l ++ cont))
    (hNextLimb : findLabel l.lNextLimb prog =
      some (mulModFromNextLimb l ++ cont))
    (hBPTR : (loadWord St.memory BPTR).toNat = bptr)
    (haw : 0x1f40 ≤ 32 * St.activeWords.toNat)
    (hn32 : n ≤ 32) (hbptrN : bptr + 32 * n ≤ Ncell)
    (hh : 0 < h) (hhn : h < n)
    (hHI : (loadWord St.memory HIcell).toNat = h)
    (hT1 : (loadWord St.memory T1).toNat = 0)
    (hval : RepresentsY St.memory OUT n
      ((a * (b / 2 ^ (256 * h + 0))) % m))
    (hacc : yLimbs St.memory ACC n = limbDigits n a)
    (hbs : yLimbs St.memory bptr n = bs)
    (hmod : yLimbs St.memory MOD n = limbDigits n m)
    (hN : (loadWord St.memory Ncell).toNat = n)
    (hkeeps : MulModKeeps St.memory M₀ n)
    (hbsd : ∀ d ∈ bs, d < radix) (hbslen : bs.length = n) :
    ∃ St', ASteps prog
        ⟨mulModFromBits l ++ cont, σ, St⟩
        ⟨mulModFromBits l ++ cont, σ, St'⟩ ∧
      (loadWord St'.memory HIcell).toNat = h - 1 ∧
      (loadWord St'.memory T1).toNat = 256 ∧
      (loadWord St'.memory T0).toNat = lget bs (h - 1) ∧
      RepresentsY St'.memory OUT n
        ((a * (b / 2 ^ (256 * (h - 1) + 256))) % m) ∧
      yLimbs St'.memory ACC n = limbDigits n a ∧
      yLimbs St'.memory bptr n = bs ∧
      yLimbs St'.memory MOD n = limbDigits n m ∧
      (loadWord St'.memory Ncell).toNat = n ∧
      MulModKeeps St'.memory M₀ n ∧
      St'.activeWords = St.activeWords ∧ St'.env = St.env := by
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hOUTlit : (OUT : Nat) = 0xc00 := rfl
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hMODlit : (MOD : Nat) = 0 := rfl
  have hHIlit : (HIcell : Nat) = 0x1d80 := rfl
  have hT0lit : (T0 : Nat) = 0x1dc0 := rfl
  have hT1lit : (T1 : Nat) = 0x1de0 := rfl
  have hlimb : (loadWord St.memory (bptr + 32 * (h - 1))).toNat =
      lget bs (h - 1) :=
    yLimb_lget (show h - 1 < n by omega) hbs (by omega)
  have hlimb256 : lget bs (h - 1) < 2 ^ 256 := by
    have hlt : lget bs (h - 1) < radix :=
      hbsd _ (by
        rw [lget_eq (show h - 1 < bs.length by omega)]
        exact mem_getElem (show h - 1 < bs.length by omega))
    rw [hradius] at hlt
    exact hlt
  have hlimbw : loadWord St.memory (bptr + 32 * (h - 1)) =
      BitVec.ofNat 256 (lget bs (h - 1)) :=
    word_of_toNat hlimb hlimb256
  have haddr : bptr + 32 * (h - 1) < 2 ^ 256 := by
    have hNpow := Ncell_lt_pow
    omega
  have hBitsTop := hBits
  rw [mulModBitsTop_eq] at hBitsTop
  have hNextTop := hNextLimb
  rw [mulModFromNextLimb_eq2, mulModNextLimbBody_eq] at hNextTop
  have hj1 : evalExpr (.load T1) St = 0 := by
    show loadWord St.memory T1 = 0
    rw [word_of_toNat hT1 (by omega)]
    rfl
  have s1 := jumpIfZ_taken (prog := prog) (σ := σ) (e := .load T1)
    (l := l.lNextLimb)
    (k := store T1 (.bin .sub (.load T1) (.imm 1)) ++
      mmCallSite OUT OUT l.lSqRet l.lamEntry ++
      jumpIfZ (bitTestOf T0 T1) l.lBits ++
      mmCallSite OUT ACC l.lAddRet l.lamEntry ++
      [.jump l.lBits] ++
      [.label l.lNextLimb] ++
      jumpIfZ (.load HIcell) l.lDone ++
      store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
      store T1 (.imm 256) ++
      store T0 (loadAt (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell)))) ++
      [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ cont)
    (exprOK_load_cell' haw (by simp [fragCells])) hj1 hNextTop
  have hj2 : evalExpr (.load HIcell) St ≠ 0 := by
    show loadWord St.memory HIcell ≠ 0
    rw [word_of_toNat hHI (by omega)]
    exact ofNat_ne_zero (by omega) (by omega)
  have s2 := jumpIfZ_fall (prog := prog) (σ := σ)
    (e := .load HIcell) (l := l.lDone)
    (k := store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
      store T1 (.imm 256) ++
      store T0 (loadAt (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell)))) ++
      [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ cont)
    (exprOK_load_cell' haw (by simp [fragCells])) hj2
  have hevHI : evalExpr (.bin .sub (.load HIcell) (.imm 1)) St =
      BitVec.ofNat 256 (h - 1) := by
    show loadWord St.memory HIcell - BitVec.ofNat 256 1 =
      BitVec.ofNat 256 (h - 1)
    rw [word_of_toNat hHI (by omega),
      ofNat_sub_one (by omega) (by omega)]
  have s3 := store_cell_val (prog := prog) (c := HIcell)
    (e := .bin .sub (.load HIcell) (.imm 1))
    (w := BitVec.ofNat 256 (h - 1))
    (k := store T1 (.imm 256) ++
      store T0 (loadAt (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell)))) ++
      [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ cont)
    (σ := σ) hevHI
    ⟨rfl, exprOK_load_cell' haw (by simp [fragCells]), True.intro⟩
    (haw_pin haw (by simp [fragCells]))
  set S₁ : EvmState := {St with memory :=
      (storeWord St.memory HIcell (BitVec.ofNat 256 (h - 1)))} with hS₁def
  have hS₁mem : S₁.memory =
      storeWord St.memory HIcell (BitVec.ofNat 256 (h - 1)) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have s4 := store_cell_val (prog := prog) (c := T1) (e := .imm 256)
    (w := BitVec.ofNat 256 256)
    (k := store T0 (loadAt (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell)))) ++
      [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ cont)
    (σ := σ) (yst := S₁) rfl True.intro
    (haw_pin hawS₁ (by simp [fragCells]))
  set S₂ : EvmState := {S₁ with memory :=
      (storeWord S₁.memory T1 (BitVec.ofNat 256 256))} with hS₂def
  have hS₂mem : S₂.memory =
      storeWord S₁.memory T1 (BitVec.ofNat 256 256) := rfl
  have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := hawS₁
  have hHIw₂ : loadWord S₂.memory HIcell =
      BitVec.ofNat 256 (h - 1) := by
    rw [hS₂mem, loadWord_storeWord_disj (p := T1) (q := HIcell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord]
  have hBPTRw₂ : loadWord S₂.memory BPTR = BitVec.ofNat 256 bptr := by
    rw [hS₂mem, loadWord_storeWord_disj (p := T1) (q := BPTR)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := HIcell) (q := BPTR)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact BPTR_word hBPTR (by omega)
  have hBPTRw₂ : loadWord S₂.memory BPTR = BitVec.ofNat 256 bptr := by
    rw [hS₂mem, loadWord_storeWord_disj (p := T1) (q := BPTR)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := HIcell) (q := BPTR)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact BPTR_word hBPTR (by omega)
  have hload : evalExpr (loadAt (.bin .add (.load BPTR)
      (.bin .mul (.imm 32) (.load HIcell)))) S₂ =
      loadWord S₂.memory (bptr + 32 * (h - 1)) :=
    eval_loadAt_bptr hBPTRw₂ hHIw₂ haddr
  have hlimbw₂ : loadWord S₂.memory (bptr + 32 * (h - 1)) =
      BitVec.ofNat 256 (lget bs (h - 1)) := by
    rw [hS₂mem, loadWord_storeWord_disj (p := T1)
      (q := bptr + 32 * (h - 1)) (Or.inr (by omega)),
      hS₁mem, loadWord_storeWord_disj (p := HIcell)
      (q := bptr + 32 * (h - 1)) (Or.inr (by omega))]
    exact hlimbw
  have hokval : exprOK (loadAt (.bin .add (.load BPTR)
      (.bin .mul (.imm 32) (.load HIcell)))) S₂ :=
    ⟨by
      show (evalExpr (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell))) S₂).toNat + 32 ≤
          32 * S₂.activeWords.toNat
      rw [eval_addr_bptr hBPTRw₂ hHIw₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr]
      omega,
      rfl, exprOK_load_cell' hawS₂ (by simp [fragCells]), rfl, True.intro,
      exprOK_load_cell' hawS₂ (by simp [fragCells])⟩
  have s5 := store_cell_val (prog := prog) (c := T0)
    (e := loadAt (.bin .add (.load BPTR)
      (.bin .mul (.imm 32) (.load HIcell))))
    (w := loadWord S₂.memory (bptr + 32 * (h - 1)))
    (k := [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ cont)
    (σ := σ) (yst := S₂) hload hokval
    (haw_pin hawS₂ (by simp [fragCells]))
  set S₃ : EvmState := {S₂ with memory :=
      (storeWord S₂.memory T0
        (loadWord S₂.memory (bptr + 32 * (h - 1))))} with hS₃def
  have hS₃mem : S₃.memory =
      storeWord S₂.memory T0
        (loadWord S₂.memory (bptr + 32 * (h - 1))) := rfl
  have s6 := ASteps.single (astep_jump (prog := prog) (l := l.lBits)
    (c' := jumpIfZ (.load T1) l.lNextLimb ++
      store T1 (.bin .sub (.load T1) (.imm 1)) ++
      mmCallSite OUT OUT l.lSqRet l.lamEntry ++
      jumpIfZ (bitTestOf T0 T1) l.lBits ++
      mmCallSite OUT ACC l.lAddRet l.lamEntry ++
      [.jump l.lBits] ++
      [.label l.lNextLimb] ++
      jumpIfZ (.load HIcell) l.lDone ++
      store HIcell (.bin .sub (.load HIcell) (.imm 1)) ++
      store T1 (.imm 256) ++
      store T0 (loadAt (.bin .add (.load BPTR)
        (.bin .mul (.imm 32) (.load HIcell)))) ++
      [.jump l.lBits] ++
      [.label l.lZero] ++
      mulModFromZero l ++ cont)
    (k := [.label l.lZero] ++ mulModFromZero l ++ cont)
    (σ := σ) (yst := S₃) hBitsTop)
  have hsteps : ASteps prog
      ⟨mulModFromBits l ++ cont, σ, St⟩
      ⟨mulModFromBits l ++ cont, σ, S₃⟩ := by
    rw [mulModBitsTop_eq]
    exact (((((s1.trans s2).trans s3).trans s4).trans s5).trans s6)
  have hHI' : (loadWord S₃.memory HIcell).toNat = h - 1 := by
    rw [hS₃mem, loadWord_storeWord_disj (p := T0) (q := HIcell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hHIw₂, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hT1' : (loadWord S₃.memory T1).toNat = 256 := by
    rw [hS₃mem, loadWord_storeWord_disj (p := T0) (q := T1)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by decide)]
  have hT0' : (loadWord S₃.memory T0).toNat = lget bs (h - 1) := by
    rw [hS₃mem, loadWord_storeWord, hlimbw₂, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hlimb256]
  have hN' : (loadWord S₃.memory Ncell).toNat = n := by
    rw [hS₃mem, loadWord_storeWord_disj (p := T0) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := T1) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := HIcell) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN
  have hOUT : yLimbs S₃.memory OUT n = yLimbs St.memory OUT n := by
    rw [hS₃mem, yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega)),
      hS₂mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega)),
      hS₁mem, yLimbs_storeWord_disjoint (q := HIcell) (Or.inr (by omega))]
  have hACC : yLimbs S₃.memory ACC n = yLimbs St.memory ACC n := by
    rw [hS₃mem, yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega)),
      hS₂mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega)),
      hS₁mem, yLimbs_storeWord_disjoint (q := HIcell) (Or.inr (by omega))]
  have hB : yLimbs S₃.memory bptr n = yLimbs St.memory bptr n := by
    rw [hS₃mem, yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega)),
      hS₂mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega)),
      hS₁mem, yLimbs_storeWord_disjoint (q := HIcell) (Or.inr (by omega))]
  have hMOD : yLimbs S₃.memory MOD n = yLimbs St.memory MOD n := by
    rw [hS₃mem, yLimbs_storeWord_disjoint (q := T0) (Or.inr (by omega)),
      hS₂mem, yLimbs_storeWord_disjoint (q := T1) (Or.inr (by omega)),
      hS₁mem, yLimbs_storeWord_disjoint (q := HIcell) (Or.inr (by omega))]
  have hexp : 256 * (h - 1) + 256 = 256 * h + 0 := by omega
  have hval' : RepresentsY S₃.memory OUT n
      ((a * (b / 2 ^ (256 * (h - 1) + 256))) % m) := by
    rw [hexp]
    exact ⟨hval.1, hOUT.trans hval.2⟩
  have hkeeps' : MulModKeeps S₃.memory M₀ n :=
    mulKeeps_storeWord (mulKeeps_storeWord (mulKeeps_storeWord hkeeps
      (Or.inr (by simp [mulModScratch])))
      (Or.inr (by simp [mulModScratch])))
      (Or.inr (by simp [mulModScratch]))
  exact ⟨S₃, hsteps, hHI', hT1', hT0', hval', hACC.trans hacc,
    hB.trans hbs, hMOD.trans hmod, hN', hkeeps', rfl, rfl⟩

/-! ## The return-copy tail -/
theorem mulTail_steps (l : MulModProcLabels) (n : Nat) {σ : List AVal}
    {S : EvmState} {M₀ : Nat → UInt8}
    (hRetCopy : findLabel l.lRetCopy programAsm =
      some (mulModRetCopyBody l ++ ([.label l.lExit] ++ [.dynJump])))
    (hExit : findLabel l.lExit programAsm = some [.dynJump])
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hkeeps : MulModKeeps S.memory M₀ n) :
    ∃ S', ASteps programAsm ⟨mulModFromRet l, σ, S⟩ ⟨[.dynJump], σ, S'⟩ ∧
      yLimbs S'.memory ACC n = yLimbs S.memory OUT n ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      MulModKeeps S'.memory M₀ n ∧ S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hACClit : (ACC : Nat) = 0x800 := rfl
  have hOUTlit : (OUT : Nat) = 0xc00 := rfl
  have hNcellLit : (Ncell : Nat) = 0x1cc0 := rfl
  have hI2lit : (I2 : Nat) = 0x1e60 := rfl
  have s0 := store_cell_val (prog := programAsm) (c := I2) (e := .imm 0)
    (w := BitVec.ofNat 256 0)
    (k := [.label l.lRetCopy] ++
      (mulModRetCopyBody l ++ ([.label l.lExit] ++ [.dynJump])))
    (σ := σ) rfl True.intro (haw_pin haw (by simp [fragCells]))
  set S₁ : EvmState := {S with memory :=
      (storeWord S.memory I2 (BitVec.ofNat 256 0))} with hS₁def
  have hS₁mem : S₁.memory =
      storeWord S.memory I2 (BitVec.ofNat 256 0) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hI2₁ : (loadWord S₁.memory I2).toNat = 0 := by
    rw [hS₁mem, loadWord_storeWord, BitVec.toNat_ofNat]
  have hN₁ : (loadWord S₁.memory Ncell).toNat = n := by
    rw [hS₁mem, loadWord_storeWord_disj (p := I2) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN
  have hkeeps₁ : MulModKeeps S₁.memory M₀ n :=
    mulKeeps_storeWord hkeeps
      (Or.inr (Or.inr (Or.inr (mulScratch_add
        (show I2 ∈ addModScratch by decide)))))
  have hout₁ : yLimbs S₁.memory OUT n = yLimbs S.memory OUT n := by
    rw [hS₁mem, yLimbs_storeWord_disjoint (q := I2) (Or.inr (by omega))]
  obtain ⟨S', hcopy, haccF, hNF, houtF, hbytes, hawF, henvF⟩ :=
    mulCopyLoop_steps (dstBase := ACC) (srcBase := OUT)
      (l := {l with lCopy := l.lRetCopy})
      (xs := yLimbs S₁.memory OUT n) (out₀ := yLimbs S₁.memory ACC n)
      (n := n) (lExit := l.lExit) (c' := [.dynJump])
      (k := [.label l.lExit] ++ [.dynJump]) (σ := σ) (S := S₁)
      (hCopy := by
        simpa only [mulModRetCopyBody, mulModCopyBody] using hRetCopy)
      (hExit := hExit) hawS₁ hn hn32
      (hdstN := by omega) (hsrcN := by omega) (hds := Or.inl (by omega))
      hN₁ hI2₁ (hdstL := rfl) (hsrcL := rfl)
      (hxslen := length_yLimbs S₁.memory OUT n)
      (houtlen := length_yLimbs S₁.memory ACC n)
      (hxd := fun d hd => yLimb_lt hd)
  have hkeepsF : MulModKeeps S'.memory M₀ n := by
    refine mulKeeps_trans ?_ hkeeps₁
    intro q hq1 hq2 hq3 hq4
    exact hbytes q hq2 (hq4 I2 (mulScratch_add
      (show I2 ∈ addModScratch by decide)))
  refine ⟨S', ?_, haccF.trans hout₁, hNF, hkeepsF, by rw [hawF], henvF⟩
  simp only [mulModFromRet, mulModRetEntry, List.append_assoc]
  have slabel : ASteps programAsm
      ⟨[.label l.lRetCopy] ++
        (mulModRetCopyBody l ++ ([.label l.lExit] ++ [.dynJump])), σ, S₁⟩
      ⟨mulModRetCopyBody l ++ ([.label l.lExit] ++ [.dynJump]), σ, S₁⟩ :=
    ASteps.single (astep_label (prog := programAsm) (l := l.lRetCopy)
      (k := mulModRetCopyBody l ++ (Asm.label l.lExit :: [.dynJump]))
      (σ := σ) (yst := S₁))
  exact (s0.trans slabel).trans hcopy
end Challenge.Modexp.Submission.Proof.MulModProc
