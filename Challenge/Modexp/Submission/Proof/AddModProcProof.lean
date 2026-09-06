import Challenge.Modexp.Submission.AsmLib
import Challenge.Modexp.Submission.Proof.YulLimbs
import Challenge.Modexp.Submission.Proof.AddModMath
import Challenge.Modexp.Submission.Program

set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

/-!
# Asm-level correctness of the `addMod` *procedure*

`genProgram`'s `addModProc` section is a procedure: it is entered only through
a call site

```
store ADST (.imm dst) ++ store ASRC (.imm src) ++
[.pushLabel lret, .jump lamEntry, .label lret] ++ cont
```

(the two stores bake the operand region addresses into the `ADST`/`ASRC`
register cells per call), runs its body with the return address
`.code lret` sitting at the bottom of the stack, and returns through the
trailing `.dynJump`, which pops that address and lands at `cont`.

The body is the label-parameterized two-pass add-with-carry /
conditional-subtract / selective-copy algorithm; unlike the inlined fragment
of the previous program basis, every `dst`-region access is addressed
through the `ADST` cell (`load ADST + load AOFF`), not an immediate.

This module proves the procedure correct at the labeled-assembly machine
level (`ASteps`) in two layers:

* `amProcFrag_correct` — the *body*: from a state whose `dst` region
  represents `x`, whose `src` region represents `y`, whose `MOD` region
  represents `m` (all `n`-limb, `0 < n ≤ 32`, `0 < m`, `x < m`, `y ≤ m`),
  and whose `ADST`/`ASRC` cells hold `dst`/`src`, running the body (from
  `store C1 0` through `.label lamDone`) against any continuation `cont`
  with any stack `σ` reaches `cont` with the stack unchanged and the `dst`
  region representing `(x + y) % m`, `Ncell` still holding `n`, and every
  byte outside the `dst`/`SUBC` regions and the eight scratch cells
  (`C1, C2, I2, AOFF, AX, AY, AS, AZ`) unchanged.  (The `ADST`/`ASRC` cells
  themselves are preserved by the body; the caller's `I2` is clobbered —
  callers use `Icell` as their loop counter.)

* `addModCall_correct` — the *call site*: from
  `store ADST dst; store ASRC src; pushLabel lret; jump lamEntry` against
  the caller's continuation `cont`, the whole call returns to `cont` with
  the original stack `σ` (the return address is pushed and popped inside),
  the `dst` region representing `(x + y) % m`, `Ncell` unchanged, and every
  byte outside the `dst`/`SUBC` regions and the ten call-scratch cells
  (`ADST, ASRC, C1, C2, I2, AOFF, AX, AY, AS, AZ` — the two address
  registers are part of the calling convention) unchanged.

Both theorems are stated for an arbitrary program `prog` against which the
procedure's eight labels resolve (hypotheses `findLabel …`); callers
instantiate `prog := programAsm` (concrete labels: `lamEntry` = 42,
`lamAdd` = 43, `lamSubStart` = 44, `amSub` = 45, `lamSel` = 46,
`lamDoCopy` = 47, `lamCopy` = 48, `lamDone` = 49) and discharge the
`findLabel`/`labelDefs` facts by `decide`.

The limb-loop invariants (proved per pass below):

* **add pass** — after `i` rounds: `I2 = i`, `C1 = cᵢ` where
  `(addDigitLists (xs.take i) (ys.take i) 0) = (preᵢ, cᵢ)`, the `dst` limbs
  are `preᵢ ++ xs.drop i`, every `src` limb at position `≥ i` still reads
  `ys[j]` (this is what makes the `dst = src` doubling call site sound: the
  round reads position `i` before writing it), and the `ADST`/`ASRC` cells
  still hold `dst`/`src`.
* **sub pass** — after `i` rounds: `I2 = i`, `C2 = bᵢ` where
  `(subDigitLists (sum.take i) (ms.take i) 0) = (candᵢ, bᵢ)`, the `SUBC`
  limbs are `candᵢ ++ subc₀.drop i`, the `dst` region still holds the
  wrapped sum limbs, and `ADST` still holds `dst`.
* **copy pass** — after `i` rounds: the `dst` limbs are
  `cand.take i ++ sum.drop i`.

The final selection (`C1 ≠ 0 ∨ C2 = 0` ⇒ copy the subtraction candidate)
matches `AddModMath.addModResult`, so the value-level specification
`AddModMath.addModResult_value_le` applies verbatim (the `≤` variant: the
`src` operand may equal the modulus — the ONE region against `m = 1`).
-/

namespace Challenge.Modexp.Submission.Proof.AddModProcProof

open Challenge.Modexp.Submission
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proof.YulLimbs
open Challenge.Modexp.Submission.Proof.AddModMath
open YulEvmCompiler
open YulSemantics.EVM (U256 EvmState loadWord storeWord b2w)

/-! ## Word-level arithmetic helpers -/

/-- The wrapped sum of two words, on `Nat`. -/
theorem toNat_add_eq (a b : U256) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 256 := by
  simp

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

/-- Adding a small carry before the modulus. -/
theorem mod_add_eq (a c r : Nat) (hc : c < r) : (a % r + c) % r = (a + c) % r := by
  rw [Nat.add_mod a c r, Nat.mod_eq_of_lt hc]

/-- The wrapped word difference as the mathematical `difference`. -/
theorem sub_wrap (x y : Nat) (hx : x < 2 ^ 256) :
    (x + 2 ^ 256 - y) % 2 ^ 256 = if x < y then 2 ^ 256 + x - y else x - y := by
  by_cases h : x < y
  · have hlt : x + 2 ^ 256 - y < 2 ^ 256 := by omega
    rw [if_pos h, Nat.mod_eq_of_lt hlt]
    omega
  · have hy : y ≤ x := by omega
    have hEq : x + 2 ^ 256 - y = (x - y) + 2 ^ 256 := by omega
    rw [if_neg h, hEq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-! ## Cell and pinning helpers -/

/-- The cells used by the procedure (all 32-aligned, all at or above
`Ncell`, all at or below `TOP`).  Extends the inline fragment's list with
the two address registers `ADST`/`ASRC` the procedure reads. -/
def fragCells : List Nat :=
  [Ncell, Icell, Jcell, Wcell, C1, C2, HIcell, T0, T1, T2, ADST, ASRC, I2, AOFF, AX, AY, AS, AZ]

theorem fragCells_aligned : ∀ c ∈ fragCells, c % 32 = 0 := by decide

theorem fragCells_ge : ∀ c ∈ fragCells, Ncell ≤ c := by decide

theorem fragCells_le : ∀ c ∈ fragCells, c ≤ TOP := by decide

/-- Distinct cells sit in disjoint 32-byte windows. -/
theorem cells_disj {c d : Nat} (hc : c ∈ fragCells) (hd : d ∈ fragCells) (hne : c ≠ d) :
    c + 32 ≤ d ∨ d + 32 ≤ c := by
  have h1 := fragCells_aligned c hc
  have h2 := fragCells_aligned d hd
  omega

/-- The top cell address is below `2 ^ 256`. -/
theorem TOP_lt : (TOP : Nat) < 2 ^ 256 := by decide

/-- Every cell is pinned inside the active window. -/
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

/-- The `I2 < Ncell` exit test of a limb loop, fall-through (`i < n`). -/
theorem exitTest_fall [model : ExternalModel] {prog : List Asm} {l : Label}
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
    (exprOK_load_cell haw (by simp [fragCells]))
    (exprOK_load_cell haw (by simp [fragCells])) (by omega) (by omega) hlt

/-- The `I2 < Ncell` exit test of a limb loop, taken (`n ≤ i`). -/
theorem exitTest_taken [model : ExternalModel] {prog : List Asm} {l : Label}
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
    (exprOK_load_cell haw (by simp [fragCells]))
    (exprOK_load_cell haw (by simp [fragCells])) (by omega) (by omega) hle hfind

/-- Strict `ult` from the value level. -/
theorem ult_of_lt {a b : U256} (h : a.toNat < b.toNat) : a.ult b := by
  have hu : a.ult b = true := (BitVec.ult_iff_toNat_lt (x := a) (y := b)).mpr h
  simpa using hu

/-- Refuted `ult` from the value level. -/
theorem not_ult_of_ge {a b : U256} (h : b.toNat ≤ a.toNat) : ¬a.ult b := by
  have hu : ¬(a.ult b = true) := (BitVec.ult_iff_toNat_lt (x := a) (y := b)).not.mpr (by omega)
  simpa using hu

/-- The word-level `ult` test as a numeric `if`. -/
theorem b2w_ult_toNat (a b : U256) :
    (b2w (a.ult b)).toNat = if a.toNat < b.toNat then 1 else 0 := by
  by_cases h : a.toNat < b.toNat
  · have hu : a.ult b := ult_of_lt h
    simp [toNat_b2w_eq, hu, h]
  · have hu : ¬a.ult b := not_ult_of_ge (by omega)
    simp [toNat_b2w_eq, hu, h]

/-- `AOFF := 32 * I2`. -/
theorem store_off32_steps [model : ExternalModel] {prog : List Asm} {i : Nat}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hI2 : loadWord yst.memory I2 = BitVec.ofNat 256 i) :
    ASteps prog ⟨store AOFF (.bin .mul (.imm 32) (.load I2)) ++ k, σ, yst⟩
      ⟨k, σ, { yst with memory :=
        (storeWord yst.memory AOFF (BitVec.ofNat 256 (32 * i))) }⟩ := by
  refine store_cell_val (c := AOFF) (e := .bin .mul (.imm 32) (.load I2))
    (w := BitVec.ofNat 256 (32 * i)) ?_ ⟨rfl, True.intro,
      exprOK_load_cell haw (by simp [fragCells])⟩
    (cell_pinned haw (by simp [fragCells]))
  simp only [evalExpr, evalBin, hI2, ofNat_mul256]

/-- `I2 := I2 + 1`. -/
theorem incr_I2_steps [model : ExternalModel] {prog : List Asm} {i : Nat}
    {k : List Asm} {σ : List AVal} {yst : EvmState}
    (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hI2 : loadWord yst.memory I2 = BitVec.ofNat 256 i) (hlt : i < 2 ^ 256) :
    ASteps prog ⟨store I2 (.bin .add (.load I2) (.imm 1)) ++ k, σ, yst⟩
      ⟨k, σ, { yst with memory :=
        (storeWord yst.memory I2 (BitVec.ofNat 256 (i + 1))) }⟩ := by
  refine store_cell_val (c := I2) (e := .bin .add (.load I2) (.imm 1))
    (w := BitVec.ofNat 256 (i + 1)) ?_
    ⟨rfl, exprOK_load_cell haw (by simp [fragCells]), True.intro⟩
    (cell_pinned haw (by simp [fragCells]))
  simp only [evalExpr, evalBin, hI2, ofNat_add256]

/-- An `mload` at `base + (cell value)`, with the cell value already read. -/
theorem eval_mload_add {S : EvmState} {base c k : Nat}
    (hw : loadWord S.memory c = BitVec.ofNat 256 k) (hlt : base + k < 2 ^ 256) :
    evalExpr (loadAt (.bin .add (.imm base) (.load c))) S = loadWord S.memory (base + k) := by
  show loadWord S.memory (evalExpr (.bin .add (.imm base) (.load c)) S).toNat = _
  rw [show evalExpr (.bin .add (.imm base) (.load c)) S = BitVec.ofNat 256 (base + k) from by
      simp only [evalExpr, evalBin, hw, ofNat_add256],
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The sum of two cell words. -/
theorem eval_add_loads (S : EvmState) (c d x y : Nat)
    (hc : loadWord S.memory c = BitVec.ofNat 256 x)
    (hd : loadWord S.memory d = BitVec.ofNat 256 y) :
    evalExpr (.bin .add (.load c) (.load d)) S = BitVec.ofNat 256 (x + y) := by
  simp only [evalExpr, evalBin, hc, hd, ofNat_add256]

/-- An `mload` at `(cell value) + (cell value)` — the procedure's
`ADST`/`AOFF` addressing. -/
theorem eval_mload_addCells {S : EvmState} {c d x y : Nat}
    (hc : loadWord S.memory c = BitVec.ofNat 256 x)
    (hd : loadWord S.memory d = BitVec.ofNat 256 y)
    (hlt : x + y < 2 ^ 256) :
    evalExpr (loadAt (.bin .add (.load c) (.load d))) S = loadWord S.memory (x + y) := by
  show loadWord S.memory (evalExpr (.bin .add (.load c) (.load d)) S).toNat = _
  rw [eval_add_loads S c d x y hc hd, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- The difference of two cell words. -/
theorem eval_sub_loads (S : EvmState) (c d x y : Nat)
    (hc : loadWord S.memory c = BitVec.ofNat 256 x)
    (hd : loadWord S.memory d = BitVec.ofNat 256 y) :
    evalExpr (.bin .sub (.load c) (.load d)) S =
      BitVec.ofNat 256 x - BitVec.ofNat 256 y := by
  simp only [evalExpr, evalBin, hc, hd]

/-- The address `base + (cell value)` as an `ofNat` word. -/
theorem eval_addr_add {S : EvmState} {base c k : Nat}
    (hw : loadWord S.memory c = BitVec.ofNat 256 k) :
    evalExpr (.bin .add (.imm base) (.load c)) S = BitVec.ofNat 256 (base + k) := by
  simp only [evalExpr, evalBin, hw, ofNat_add256]

/-! ## Limb-level helpers -/

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

/-! ## The procedure, decomposed -/

/-- The procedure's eight labels. -/
structure AddModProcLabels where
  lEntry : Nat
  lAdd : Nat
  lSubStart : Nat
  lSub : Nat
  lSel : Nat
  lDoCopy : Nat
  lCopy : Nat
  lDone : Nat

/-- The addition-pass loop body: from just after `.label l.lAdd` to
`.label l.lSubStart` (exclusive).  The `dst`/`src` region addresses come
from the `ADST`/`ASRC` cells. -/
def amAddBody (l : AddModProcLabels) : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) l.lSubStart ++
  store AOFF (.bin .mul (.imm 32) (.load I2)) ++
  store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
  store AY (loadAt (.bin .add (.load ASRC) (.load AOFF))) ++
  store AS (.bin .add (.load AX) (.load AY)) ++
  store AZ (.bin .add (.load AS) (.load C1)) ++
  store C1 (.bin .or (.bin .lt (.load AS) (.load AX)) (.bin .lt (.load AZ) (.load AS))) ++
  storeAt (.bin .add (.load ADST) (.load AOFF)) (.load AZ) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lAdd]

/-- The subtraction-pass loop body: from just after `.label l.lSub` to
`.label l.lSel` (exclusive). -/
def amSubBody (l : AddModProcLabels) : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) l.lSel ++
  store AOFF (.bin .mul (.imm 32) (.load I2)) ++
  store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
  store AY (loadAt (.load AOFF)) ++
  store AS (.bin .sub (.load AX) (.load AY)) ++
  store AZ (.bin .sub (.load AS) (.load C2)) ++
  store C2 (.bin .or (.bin .lt (.load AX) (.load AY)) (.bin .lt (.load AS) (.load C2))) ++
  storeAt (.bin .add (.imm SUBC) (.load AOFF)) (.load AZ) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lSub]

/-- The selection code: from just after `.label l.lSel` to `.label l.lDoCopy`
(exclusive). -/
def amSelBody (l : AddModProcLabels) : List Asm :=
  jumpIfNz (.bin .or (.load C1) (.un .iszero (.load C2))) l.lDoCopy ++
  [.jump l.lDone]

/-- The copy loop body: from just after `.label l.lCopy` to `.label l.lDone`
(exclusive). -/
def amCopyBody (l : AddModProcLabels) : List Asm :=
  jumpUnlessLt (.load I2) (.load Ncell) l.lDone ++
  storeAt (.bin .add (.load ADST) (.bin .mul (.imm 32) (.load I2)))
    (loadAt (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2)))) ++
  store I2 (.bin .add (.load I2) (.imm 1)) ++
  [.jump l.lCopy]

/-- The fragment from `.label l.lDone` onward. -/
def amFromDone (l : AddModProcLabels) : List Asm :=
  [.label l.lDone]

/-- The fragment from `.label l.lCopy` onward. -/
def amFromCopy (l : AddModProcLabels) : List Asm :=
  [.label l.lCopy] ++ amCopyBody l ++ amFromDone l

/-- The fragment from `.label l.lDoCopy` onward. -/
def amFromDoCopy (l : AddModProcLabels) : List Asm :=
  [.label l.lDoCopy] ++ store I2 (.imm 0) ++ amFromCopy l

/-- The fragment from `.label l.lSel` onward. -/
def amFromSel (l : AddModProcLabels) : List Asm :=
  [.label l.lSel] ++ amSelBody l ++ amFromDoCopy l

/-- The fragment from `.label l.lSub` onward. -/
def amFromSub (l : AddModProcLabels) : List Asm :=
  [.label l.lSub] ++ amSubBody l ++ amFromSel l

/-- The fragment from `.label l.lSubStart` onward. -/
def amFromSubStart (l : AddModProcLabels) : List Asm :=
  [.label l.lSubStart] ++ store C2 (.imm 0) ++ store I2 (.imm 0) ++
  amFromSub l

/-- The procedure body after the entry label, up to (and excluding) the
final `.dynJump`: from `store C1 (.imm 0)` through `.label l.lDone`. -/
def amProcFrag (l : AddModProcLabels) : List Asm :=
  store C1 (.imm 0) ++ store I2 (.imm 0) ++ [.label l.lAdd] ++
  amAddBody l ++ amFromSubStart l

/-- The fragment splits at its labels. -/
theorem amProcFrag_split (l : AddModProcLabels) :
    amProcFrag l =
      store C1 (.imm 0) ++ store I2 (.imm 0) ++ [.label l.lAdd] ++
      amAddBody l ++ amFromSubStart l := by
  simp only [amProcFrag, amFromSubStart, amFromSub, amFromSel, amFromDoCopy,
    amFromCopy, amFromDone, amAddBody, amSubBody, amSelBody, amCopyBody, store,
    storeAt, jumpUnlessLt, jumpIfNz, loadAt, List.append_assoc]

theorem amAddBody_eq (l : AddModProcLabels) (k : List Asm) :
    amAddBody l ++ k =
      jumpUnlessLt (.load I2) (.load Ncell) l.lSubStart ++
      (store AOFF (.bin .mul (.imm 32) (.load I2)) ++
      store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
      store AY (loadAt (.bin .add (.load ASRC) (.load AOFF))) ++
      store AS (.bin .add (.load AX) (.load AY)) ++
      store AZ (.bin .add (.load AS) (.load C1)) ++
      store C1 (.bin .or (.bin .lt (.load AS) (.load AX)) (.bin .lt (.load AZ) (.load AS))) ++
      storeAt (.bin .add (.load ADST) (.load AOFF)) (.load AZ) ++
      store I2 (.bin .add (.load I2) (.imm 1)) ++
      ([.jump l.lAdd] ++ k)) := rfl

theorem amSubBody_eq (l : AddModProcLabels) (k : List Asm) :
    amSubBody l ++ k =
      jumpUnlessLt (.load I2) (.load Ncell) l.lSel ++
      (store AOFF (.bin .mul (.imm 32) (.load I2)) ++
      store AX (loadAt (.bin .add (.load ADST) (.load AOFF))) ++
      store AY (loadAt (.load AOFF)) ++
      store AS (.bin .sub (.load AX) (.load AY)) ++
      store AZ (.bin .sub (.load AS) (.load C2)) ++
      store C2 (.bin .or (.bin .lt (.load AX) (.load AY)) (.bin .lt (.load AS) (.load C2))) ++
      storeAt (.bin .add (.imm SUBC) (.load AOFF)) (.load AZ) ++
      store I2 (.bin .add (.load I2) (.imm 1)) ++
      ([.jump l.lSub] ++ k)) := rfl

theorem amCopyBody_eq (l : AddModProcLabels) (k : List Asm) :
    amCopyBody l ++ k =
      jumpUnlessLt (.load I2) (.load Ncell) l.lDone ++
      (storeAt (.bin .add (.load ADST) (.bin .mul (.imm 32) (.load I2)))
        (loadAt (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2)))) ++
      store I2 (.bin .add (.load I2) (.imm 1)) ++
      ([.jump l.lCopy] ++ k)) := rfl

/-! ## The scratch frame -/

/-- The cells the procedure body writes. -/
def addModScratch : List Nat := [C1, C2, I2, AOFF, AX, AY, AS, AZ]

/-- The cells a full call sequence writes (the two address registers are
part of the calling convention). -/
def addModCallScratch : List Nat := [ADST, ASRC, C1, C2, I2, AOFF, AX, AY, AS, AZ]

theorem scratch_cells_lit : ∀ c ∈ [C1, C2, I2, AOFF, AX, AY, AS, AZ],
    c ∈ [Ncell, Icell, Jcell, Wcell, C1, C2, HIcell, T0, T1, T2, ADST, ASRC,
      I2, AOFF, AX, AY, AS, AZ] := by
  decide

theorem arc_ne_lit : ∀ c ∈ [I2, C1, C2, AZ, AS, AY, AX, AOFF], c ≠ Ncell := by
  decide

/-- The round cells avoid the two address registers. -/
theorem arc_ne_adst : ∀ c ∈ [I2, C1, C2, AZ, AS, AY, AX, AOFF], c ≠ ADST := by decide

theorem arc_ne_asrc : ∀ c ∈ [I2, C1, C2, AZ, AS, AY, AX, AOFF], c ≠ ASRC := by decide

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

/-- The cells written by one round of the addition or subtraction pass (the
region store is accounted separately). -/
def addRoundCells : List Nat := [I2, C1, C2, AZ, AS, AY, AX, AOFF]

theorem addRoundCells_cells {c : Nat} (h : c ∈ addRoundCells) : c ∈ fragCells := by
  have h1 : ∀ c ∈ [I2, C1, C2, AZ, AS, AY, AX, AOFF],
      c ∈ [Ncell, Icell, Jcell, Wcell, C1, C2, HIcell, T0, T1, T2, ADST, ASRC,
        I2, AOFF, AX, AY, AS, AZ] := by
    decide
  unfold addRoundCells at h
  exact h1 c h

theorem addRoundCells_ne {cc : Nat} (hcc : cc ∈ addRoundCells) : cc ≠ Ncell := by
  unfold addRoundCells at hcc
  exact arc_ne_lit cc hcc

theorem addRoundCells_neADST {cc : Nat} (hcc : cc ∈ addRoundCells) : cc ≠ ADST := by
  unfold addRoundCells at hcc
  exact arc_ne_adst cc hcc

theorem addRoundCells_neASRC {cc : Nat} (hcc : cc ∈ addRoundCells) : cc ≠ ASRC := by
  unfold addRoundCells at hcc
  exact arc_ne_asrc cc hcc

theorem addRoundCells_ge {c : Nat} (h : c ∈ addRoundCells) : Ncell ≤ c :=
  fragCells_ge c (addRoundCells_cells h)

/-- One round of the addition pass: reads `dst[i]` and `src[i]` (both through
the `ADST`/`ASRC` cells), writes the wrapped sum limb and the new carry, and
increments `I2`.  The continuation `k` is the loop's back-jump target.  The
round maintains the scratch frame against the original memory `M₀` and the
two address-register cells.  Limb positions inside the invariant are
accessed via the total `lget`, avoiding index side conditions. -/
theorem addRound_steps [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (xs ys : List Nat) (n i : Nat)
    (pre : List Nat) (c : Nat) {subc₀ : List Nat} {M₀ : Nat → UInt8}
    {k : List Asm} {σ : List AVal} {S : EvmState}
    (hAdd : findLabel l.lAdd prog = some (amAddBody l ++ k))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hi : i < n) (hn32 : n ≤ 32)
    (hdstN : dst + 32 * n ≤ Ncell) (hsrcN : src + 32 * n ≤ Ncell)
    (hsubcDst : dst + 32 * n ≤ SUBC)
    (hds : src + 32 * n ≤ dst ∨ dst + 32 * n ≤ src ∨ src = dst)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = i)
    (hle : c ≤ 1)
    (hC1 : (loadWord S.memory C1).toNat = c)
    (hADST : loadWord S.memory ADST = BitVec.ofNat 256 dst)
    (hASRC : loadWord S.memory ASRC = BitVec.ofNat 256 src)
    (hdef : addDigitLists (xs.take i) (ys.take i) 0 = (pre, c))
    (hdstL : yLimbs S.memory dst n = pre ++ xs.drop i)
    (hxlen : xs.length = n) (hylen : ys.length = n)
    (hxd : lget xs i < radix) (hyd : lget ys i < radix)
    (hsrcread : ∀ j, i ≤ j → j < n →
      (loadWord S.memory (src + 32 * j)).toNat = lget ys j)
    (hsubcL : yLimbs S.memory SUBC n = subc₀)
    (hkeeps : AddModKeeps S.memory M₀ dst n) :
    ∃ S', ASteps prog ⟨amAddBody l ++ k, σ, S⟩
        ⟨amAddBody l ++ k, σ, S'⟩ ∧
      (loadWord S'.memory I2).toNat = i + 1 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      (loadWord S'.memory C1).toNat = (addDigitLists (xs.take (i + 1)) (ys.take (i + 1)) 0).2 ∧
      (addDigitLists (xs.take (i + 1)) (ys.take (i + 1)) 0).2 ≤ 1 ∧
      yLimbs S'.memory dst n =
        (addDigitLists (xs.take (i + 1)) (ys.take (i + 1)) 0).1 ++ xs.drop (i + 1) ∧
      (∀ j, i + 1 ≤ j → j < n →
        (loadWord S'.memory (src + 32 * j)).toNat = lget ys j) ∧
      AddModKeeps S'.memory M₀ dst n ∧
      yLimbs S'.memory SUBC n = subc₀ ∧
      loadWord S'.memory ADST = BitVec.ofNat 256 dst ∧
      loadWord S'.memory ASRC = BitVec.ofNat 256 src ∧
      S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hr : radix = 2 ^ 256 := rfl
  have hrpos : 0 < radix := radix_pos
  have hncell : Ncell = 0x1cc0 := rfl
  have hAOFFc : AOFF = 0x1e80 := rfl
  have hAXc : AX = 0x1ea0 := rfl
  have hAYc : AY = 0x1ec0 := rfl
  have hASc : AS = 0x1ee0 := rfl
  have hAZc : AZ = 0x1f00 := rfl
  have hC1c : C1 = 0x1d40 := rfl
  have hI2c : I2 = 0x1e60 := rfl
  have hADSTc : ADST = 0x1e20 := rfl
  have hASRCc : ASRC = 0x1e40 := rfl
  have hmod0 : (MOD : Nat) = 0 := rfl
  have hnclt : (0x1cc0 : Nat) < 2 ^ 256 := by decide
  have hi256 : i < 2 ^ 256 := by omega
  have hxlen' : i < xs.length := by omega
  have hylen' : i < ys.length := by omega
  have hxi : lget xs i = xs[i]'hxlen' := lget_eq hxlen'
  have hyi : lget ys i = ys[i]'hylen' := lget_eq hylen'
  have htakelen : (xs.take i).length = i := by rw [List.length_take]; omega
  have htakelenY : (ys.take i).length = i := by rw [List.length_take]; omega
  have hprelen : pre.length = i := by
    have h := length_addDigitLists_left (xs := xs.take i) (ys := ys.take i)
      (carry := 0) (by simp [htakelen, htakelenY])
    rw [hdef] at h
    have h2 : pre.length = (xs.take i).length := by simpa using h
    rwa [htakelen] at h2
  -- the eight states of one round
  set S₁ : EvmState := {S with memory :=
    (storeWord S.memory AOFF (BitVec.ofNat 256 (32 * i)))} with hS₁def
  set S₂ : EvmState := {S₁ with memory :=
    (storeWord S₁.memory AX (BitVec.ofNat 256 (lget xs i)))} with hS₂def
  set S₃ : EvmState := {S₂ with memory :=
    (storeWord S₂.memory AY (BitVec.ofNat 256 (lget ys i)))} with hS₃def
  set S₄ : EvmState := {S₃ with memory :=
    (storeWord S₃.memory AS (BitVec.ofNat 256 (lget xs i + lget ys i)))} with hS₄def
  set S₅ : EvmState := {S₄ with memory :=
    (storeWord S₄.memory AZ (BitVec.ofNat 256 (lget xs i + lget ys i + c)))} with hS₅def
  set S₆ : EvmState := {S₅ with memory :=
    (storeWord S₅.memory C1
      (BitVec.ofNat 256 ((lget xs i + lget ys i + c) / radix)))} with hS₆def
  set S₇ : EvmState := {S₆ with memory :=
    (storeWord S₆.memory (dst + 32 * i)
      (BitVec.ofNat 256 (lget xs i + lget ys i + c)))} with hS₇def
  set S₈ : EvmState := {S₇ with memory :=
    (storeWord S₇.memory I2 (BitVec.ofNat 256 (i + 1)))} with hS₈def
  have hS₁mem : S₁.memory =
      storeWord S.memory AOFF (BitVec.ofNat 256 (32 * i)) := rfl
  have hS₂mem : S₂.memory =
      storeWord S₁.memory AX (BitVec.ofNat 256 (lget xs i)) := rfl
  have hS₃mem : S₃.memory =
      storeWord S₂.memory AY (BitVec.ofNat 256 (lget ys i)) := rfl
  have hS₄mem : S₄.memory =
      storeWord S₃.memory AS (BitVec.ofNat 256 (lget xs i + lget ys i)) := rfl
  have hS₅mem : S₅.memory =
      storeWord S₄.memory AZ (BitVec.ofNat 256 (lget xs i + lget ys i + c)) := rfl
  have hS₆mem : S₆.memory =
      storeWord S₅.memory C1
        (BitVec.ofNat 256 ((lget xs i + lget ys i + c) / radix)) := rfl
  have hS₇mem : S₇.memory =
      storeWord S₆.memory (dst + 32 * i)
        (BitVec.ofNat 256 (lget xs i + lget ys i + c)) := rfl
  have hS₈mem : S₈.memory =
      storeWord S₇.memory I2 (BitVec.ofNat 256 (i + 1)) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := haw
  have hawS₃ : 0x1f40 ≤ 32 * S₃.activeWords.toNat := haw
  have hawS₄ : 0x1f40 ≤ 32 * S₄.activeWords.toNat := haw
  have hawS₅ : 0x1f40 ≤ 32 * S₅.activeWords.toNat := haw
  have hawS₆ : 0x1f40 ≤ 32 * S₆.activeWords.toNat := haw
  have hawS₇ : 0x1f40 ≤ 32 * S₇.activeWords.toNat := haw
  have hawS₈ : 0x1f40 ≤ 32 * S₈.activeWords.toNat := haw
  -- word values and limb reads
  have hI2w : loadWord S.memory I2 = BitVec.ofNat 256 i := word_of_toNat hI2 hi256
  have hC1w : loadWord S.memory C1 = BitVec.ofNat 256 c := word_of_toNat hC1 (by omega)
  have hxL : (loadWord S.memory (dst + 32 * i)).toNat = lget xs i := by
    have h1 : (loadWord S.memory (dst + 32 * i)).toNat = lget (pre ++ xs.drop i) i :=
      yLimb_lget hi hdstL (by rw [List.length_append, List.length_drop]; omega)
    rw [h1, lget_append_drop hprelen hxlen']
  have hyL : (loadWord S.memory (src + 32 * i)).toNat = lget ys i :=
    hsrcread i (le_refl i) hi
  have hxw : loadWord S.memory (dst + 32 * i) = BitVec.ofNat 256 (lget xs i) :=
    word_of_toNat hxL (by omega)
  have hyw : loadWord S.memory (src + 32 * i) = BitVec.ofNat 256 (lget ys i) :=
    word_of_toNat hyL (by omega)
  have hdsti : dst + 32 * i < 2 ^ 256 := by omega
  have hsrci : src + 32 * i < 2 ^ 256 := by omega
  -- arithmetic facts about the round
  have hcarryBits := addCarryBits hxd hyd hle
  have hcarryLt : (lget xs i + lget ys i + c) / radix ≤ 1 := by
    rw [Nat.div_le_iff_le_mul radix_pos]
    omega
  -- per-state value facts
  have hAOFF1 : loadWord S₁.memory AOFF = BitVec.ofNat 256 (32 * i) := by
    rw [hS₁mem]; exact loadWord_storeWord _ _ _
  have hdisjdst : loadWord S₁.memory (dst + 32 * i) =
      loadWord S.memory (dst + 32 * i) := by
    rw [hS₁mem]
    exact loadWord_storeWord_disj (p := AOFF) (q := dst + 32 * i) (by omega)
  have hdisjsrc : loadWord S₁.memory (src + 32 * i) =
      loadWord S.memory (src + 32 * i) := by
    rw [hS₁mem]
    exact loadWord_storeWord_disj (p := AOFF) (q := src + 32 * i) (by omega)
  have hADST1 : loadWord S₁.memory ADST = BitVec.ofNat 256 dst := by
    rw [hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hADST
  have hASRC1 : loadWord S₁.memory ASRC = BitVec.ofNat 256 src := by
    rw [hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := ASRC)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hASRC
  have hAXval : evalExpr (loadAt (.bin .add (.load ADST) (.load AOFF))) S₁
      = BitVec.ofNat 256 (lget xs i) := by
    rw [eval_mload_addCells hADST1 hAOFF1 hdsti, hdisjdst, hxw]
  have hAXaddrN : (evalExpr (.bin .add (.load ADST) (.load AOFF)) S₁).toNat
      = dst + 32 * i := by
    rw [eval_add_loads S₁ ADST AOFF dst (32 * i) hADST1 hAOFF1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdsti]
  have hAOFF2 : loadWord S₂.memory AOFF = BitVec.ofNat 256 (32 * i) := by
    rw [hS₂mem, loadWord_storeWord_disj (p := AX) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAOFF1
  have hASRC2 : loadWord S₂.memory ASRC = BitVec.ofNat 256 src := by
    rw [hS₂mem, loadWord_storeWord_disj (p := AX) (q := ASRC)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hASRC1]
  have hdisjsrc₂ : loadWord S₂.memory (src + 32 * i) =
      loadWord S.memory (src + 32 * i) := by
    rw [hS₂mem, loadWord_storeWord_disj (p := AX) (q := src + 32 * i) (by omega),
      hdisjsrc]
  have hAYval : evalExpr (loadAt (.bin .add (.load ASRC) (.load AOFF))) S₂
      = BitVec.ofNat 256 (lget ys i) := by
    rw [eval_mload_addCells hASRC2 hAOFF2 hsrci, hdisjsrc₂, hyw]
  have hAYaddrN : (evalExpr (.bin .add (.load ASRC) (.load AOFF)) S₂).toNat
      = src + 32 * i := by
    rw [eval_add_loads S₂ ASRC AOFF src (32 * i) hASRC2 hAOFF2, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hsrci]
  have hAX3 : loadWord S₃.memory AX = BitVec.ofNat 256 (lget xs i) := by
    rw [hS₃mem, loadWord_storeWord_disj (p := AY) (q := AX) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hS₂mem]
    exact loadWord_storeWord _ _ _
  have hAY3 : loadWord S₃.memory AY = BitVec.ofNat 256 (lget ys i) := by
    rw [hS₃mem]; exact loadWord_storeWord _ _ _
  have hAS4 : loadWord S₄.memory AS =
      BitVec.ofNat 256 (lget xs i + lget ys i) := by
    rw [hS₄mem]; exact loadWord_storeWord _ _ _
  have hC14 : loadWord S₄.memory C1 = BitVec.ofNat 256 c := by
    rw [hS₄mem, loadWord_storeWord_disj (p := AS) (q := C1) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := C1) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := AX) (q := C1) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := C1) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hC1w
  have hAS5 : loadWord S₅.memory AS =
      BitVec.ofNat 256 (lget xs i + lget ys i) := by
    rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AS) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hS₄mem]
    exact loadWord_storeWord _ _ _
  have hAX5 : loadWord S₅.memory AX = BitVec.ofNat 256 (lget xs i) := by
    rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AX) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := AX) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAX3
  have hAY5 : loadWord S₅.memory AY = BitVec.ofNat 256 (lget ys i) := by
    rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AY) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := AY) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAY3
  have hAZ5 : loadWord S₅.memory AZ =
      BitVec.ofNat 256 (lget xs i + lget ys i + c) := by
    rw [hS₅mem]; exact loadWord_storeWord _ _ _
  have hAS5tn : (loadWord S₅.memory AS).toNat = (lget xs i + lget ys i) % radix := by
    rw [hAS5, BitVec.toNat_ofNat, hr]
  have hAX5tn : (loadWord S₅.memory AX).toNat = lget xs i := by
    rw [hAX5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAZ5tn : (loadWord S₅.memory AZ).toNat =
      ((lget xs i + lget ys i) % radix + c) % radix := by
    rw [hAZ5, BitVec.toNat_ofNat, hr,
      ← mod_add_eq (lget xs i + lget ys i) c (2 ^ 256) (by omega)]
  have hC1val : evalExpr
        (.bin .or (.bin .lt (.load AS) (.load AX)) (.bin .lt (.load AZ) (.load AS))) S₅
      = BitVec.ofNat 256 ((lget xs i + lget ys i + c) / radix) := by
    apply word_of_toNat
    · have h1 : (evalExpr
          (.bin .or (.bin .lt (.load AS) (.load AX))
            (.bin .lt (.load AZ) (.load AS))) S₅).toNat =
          ((if (lget xs i + lget ys i) % radix < lget xs i then 1 else 0) |||
            (if ((lget xs i + lget ys i) % radix + c) % radix <
              (lget xs i + lget ys i) % radix then 1 else 0)) := by
        simp only [evalExpr, evalBin, toNat_or_eq, toNat_b2w_eq,
          BitVec.ult_iff_toNat_lt]
        rw [hAS5tn, hAX5tn, hAZ5tn]
      rw [h1, ← hcarryBits]
    · omega
  have hAOFF6 : loadWord S₆.memory AOFF = BitVec.ofNat 256 (32 * i) := by
    rw [hS₆mem, loadWord_storeWord_disj (p := C1) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAOFF2
  have hADST6 : loadWord S₆.memory ADST = BitVec.ofNat 256 dst := by
    rw [hS₆mem, loadWord_storeWord_disj (p := C1) (q := ADST) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₅mem, loadWord_storeWord_disj (p := AZ) (q := ADST) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := ADST) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := ADST) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := AX) (q := ADST) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := ADST) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hADST
  have hAZ6 : loadWord S₆.memory AZ =
      BitVec.ofNat 256 (lget xs i + lget ys i + c) := by
    rw [hS₆mem, loadWord_storeWord_disj (p := C1) (q := AZ) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hAZ5]
  have hAZval6 : evalExpr (Expr.load AZ) S₆ = BitVec.ofNat 256 (lget xs i + lget ys i + c) := by
    show loadWord S₆.memory AZ = _
    rw [hAZ6]
  have hI2₇ : loadWord S₇.memory I2 = BitVec.ofNat 256 i := by
    rw [hS₇mem, loadWord_storeWord_disj (p := dst + 32 * i) (q := I2) (by omega),
      hS₆mem, loadWord_storeWord_disj (p := C1) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₅mem, loadWord_storeWord_disj (p := AZ) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := AX) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hI2w
  -- the straight-line chain
  have hsteps : ASteps prog ⟨amAddBody l ++ k, σ, S⟩
      ⟨amAddBody l ++ k, σ, S₈⟩ := by
    rw [amAddBody_eq l k]
    refine (exitTest_fall (prog := prog) haw hN hI2 (by omega) hi).trans ?_
    refine (store_off32_steps (prog := prog) haw hI2w).trans ?_
    refine (store_cell_val (prog := prog) (c := AX)
      (e := loadAt (.bin .add (.load ADST) (.load AOFF))) (w := BitVec.ofNat 256 (lget xs i))
      hAXval ⟨(by
        rw [hAXaddrN]
        show dst + 32 * i + 32 ≤ 32 * S₁.activeWords.toNat
        omega),
        ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
          exprOK_load_cell haw (by simp [fragCells])⟩⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := AY)
      (e := loadAt (.bin .add (.load ASRC) (.load AOFF))) (w := BitVec.ofNat 256 (lget ys i))
      hAYval ⟨(by
        rw [hAYaddrN]
        show src + 32 * i + 32 ≤ 32 * S₂.activeWords.toNat
        omega),
        ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
          exprOK_load_cell haw (by simp [fragCells])⟩⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := AS) (e := .bin .add (.load AX) (.load AY))
      (w := BitVec.ofNat 256 (lget xs i + lget ys i))
      (eval_add_loads S₃ AX AY _ _ hAX3 hAY3)
      ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := AZ) (e := .bin .add (.load AS) (.load C1))
      (w := BitVec.ofNat 256 (lget xs i + lget ys i + c))
      (eval_add_loads S₄ AS C1 (lget xs i + lget ys i) c hAS4 hC14)
      ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := C1)
      (e := .bin .or (.bin .lt (.load AS) (.load AX)) (.bin .lt (.load AZ) (.load AS)))
      (w := BitVec.ofNat 256 ((lget xs i + lget ys i + c) / radix)) hC1val
      ⟨rfl, ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩,
        ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
          exprOK_load_cell haw (by simp [fragCells])⟩⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (storeAt_val (prog := prog)
      (addrE := .bin .add (.load ADST) (.load AOFF)) (valE := .load AZ)
      (addr := dst + 32 * i) (w := BitVec.ofNat 256 (lget xs i + lget ys i + c))
      (eval_add_loads S₆ ADST AOFF dst (32 * i) hADST6 hAOFF6) hAZval6 hdsti
      (exprOK_load_cell haw (by simp [fragCells]))
      ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩
      (by show dst + 32 * i + 32 ≤ 32 * S₆.activeWords.toNat; omega)).trans ?_
    refine (incr_I2_steps (prog := prog) (yst := S₇) haw hI2₇ hi256).trans ?_
    exact ASteps.single (astep_jump hAdd)
  -- the one-step list recurrence (real `getElem` form)
  have hap : addDigitLists (xs.take (i + 1)) (ys.take (i + 1)) 0 =
      (pre ++ [(xs[i]'hxlen' + ys[i]'hylen' + c) % radix],
        (xs[i]'hxlen' + ys[i]'hylen' + c) / radix) := by
    rw [List.take_add_one, List.take_add_one,
      List.getElem?_eq_getElem hxlen', List.getElem?_eq_getElem hylen',
      Option.toList_some, Option.toList_some,
      addDigitLists_append_single (by simp [htakelen, htakelenY]), hdef]
  have hsumEq : (lget xs i + lget ys i + c) = (xs[i]'hxlen' + ys[i]'hylen' + c) := by
    rw [hxi, hyi]
  have hap1 : (addDigitLists (xs.take (i + 1)) (ys.take (i + 1)) 0).1 =
      pre ++ [(xs[i]'hxlen' + ys[i]'hylen' + c) % radix] := congrArg Prod.fst hap
  have hap2 : (addDigitLists (xs.take (i + 1)) (ys.take (i + 1)) 0).2 =
      (xs[i]'hxlen' + ys[i]'hylen' + c) / radix := congrArg Prod.snd hap
  -- byte-level: the round writes only scratch cells and limb i of dst
  have hmemEq : ∀ a, (a < dst + 32 * i ∨ dst + 32 * i + 32 ≤ a) →
      (∀ cc ∈ addRoundCells, a < cc ∨ cc + 32 ≤ a) → S₈.memory a = S.memory a := by
    intro a ha hall
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    rw [storeWord_other (hall I2 (by simp [addRoundCells])),
      storeWord_other (p := dst + 32 * i) ha,
      storeWord_other (hall C1 (by simp [addRoundCells])),
      storeWord_other (hall AZ (by simp [addRoundCells])),
      storeWord_other (hall AS (by simp [addRoundCells])),
      storeWord_other (hall AY (by simp [addRoundCells])),
      storeWord_other (hall AX (by simp [addRoundCells])),
      storeWord_other (hall AOFF (by simp [addRoundCells]))]
  have hdstReg : dst ≤ dst + 32 * i ∧ dst + 32 * i + 32 ≤ dst + 32 * n := by omega
  have hmI2 : I2 ∈ addModScratch := by decide
  have hmC1 : C1 ∈ addModScratch := by decide
  have hmC2 : C2 ∈ addModScratch := by decide
  have hmAZ : AZ ∈ addModScratch := by decide
  have hmAS : AS ∈ addModScratch := by decide
  have hmAY : AY ∈ addModScratch := by decide
  have hmAX : AX ∈ addModScratch := by decide
  have hmAOFF : AOFF ∈ addModScratch := by decide
  -- the exit-state properties
  refine ⟨S₈, hsteps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- I2
    rw [hS₈mem, loadWord_storeWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · -- Ncell
    have hNc : loadWord S₈.memory Ncell = loadWord S.memory Ncell := by
      apply loadWord_congr
      intro b hb1 hb2
      have hreg : b < dst + 32 * i ∨ dst + 32 * i + 32 ≤ b := by
        have := fragCells_ge Ncell (by simp [fragCells]); omega
      have hcells : ∀ cc ∈ addRoundCells, b < cc ∨ cc + 32 ≤ b := by
        intro cc hcc
        have hge := addRoundCells_ge hcc
        rcases cells_disj (addRoundCells_cells hcc)
            (show Ncell ∈ fragCells by simp [fragCells])
            (addRoundCells_ne hcc) with h | h
        · omega
        · omega
      exact hmemEq b hreg hcells
    rw [hNc]; exact hN
  · -- C1
    rw [hS₈mem, loadWord_storeWord_disj (p := I2) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₇mem, loadWord_storeWord_disj (p := dst + 32 * i) (q := C1) (by omega),
      hS₆mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), hap2, ← hsumEq]
  · -- carry bound
    rw [hap2, ← hsumEq]; exact hcarryLt
  · -- dst limbs
    have hset : yLimbs S₈.memory dst n =
        pre ++ [(xs[i]'hxlen' + ys[i]'hylen' + c) % radix] ++ xs.drop (i + 1) := by
      rw [hS₈mem, yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₇mem,
        yLimbs_storeWord S₆.memory dst n i hi
          (BitVec.ofNat 256 (lget xs i + lget ys i + c)),
        show (BitVec.ofNat 256 (lget xs i + lget ys i + c)).toNat =
          (xs[i]'hxlen' + ys[i]'hylen' + c) % radix from by
          rw [show (lget xs i + lget ys i + c) =
            (xs[i]'hxlen' + ys[i]'hylen' + c) from hsumEq, BitVec.toNat_ofNat, hr],
        hS₆mem, yLimbs_storeWord_disjoint (q := C1)
          (Or.inr (by have := fragCells_ge C1 (by simp [fragCells]); omega)),
        hS₅mem, yLimbs_storeWord_disjoint (q := AZ)
          (Or.inr (by have := fragCells_ge AZ (by simp [fragCells]); omega)),
        hS₄mem, yLimbs_storeWord_disjoint (q := AS)
          (Or.inr (by have := fragCells_ge AS (by simp [fragCells]); omega)),
        hS₃mem, yLimbs_storeWord_disjoint (q := AY)
          (Or.inr (by have := fragCells_ge AY (by simp [fragCells]); omega)),
        hS₂mem, yLimbs_storeWord_disjoint (q := AX)
          (Or.inr (by have := fragCells_ge AX (by simp [fragCells]); omega)),
        hS₁mem, yLimbs_storeWord_disjoint (q := AOFF)
          (Or.inr (by have := fragCells_ge AOFF (by simp [fragCells]); omega)),
        hdstL, drop_cons_of_lt xs i hxlen', set_append_mid' hprelen]
      simp
    rw [hset, hap1]
  · -- src limbs
    intro j hj1 hj2
    have hload : loadWord S₈.memory (src + 32 * j) = loadWord S.memory (src + 32 * j) := by
      apply loadWord_congr
      intro b hb1 hb2
      refine hmemEq b ?_ ?_
      · rcases hds with hcase | hcase | hcase <;> omega
      · intro cc hcc
        have hge := addRoundCells_ge hcc
        omega
    rw [hload]
    exact hsrcread j (by omega) hj2
  · -- keeps
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    exact keeps_storeWord_cell
      (keeps_storeWord_dst
        (keeps_storeWord_cell
          (keeps_storeWord_cell
            (keeps_storeWord_cell
              (keeps_storeWord_cell
                (keeps_storeWord_cell
                  (keeps_storeWord_cell hkeeps hmAOFF) hmAX) hmAY) hmAS) hmAZ) hmC1)
        hdstReg) hmI2
  · -- SUBC limbs preserved
    have hsubcEq : SUBC = 0x1400 := rfl
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    rw [yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := dst + 32 * i) (Or.inl (by omega)),
      yLimbs_storeWord_disjoint (q := C1)
        (Or.inr (by have := fragCells_ge C1 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AZ)
        (Or.inr (by have := fragCells_ge AZ (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AS)
        (Or.inr (by have := fragCells_ge AS (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AY)
        (Or.inr (by have := fragCells_ge AY (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AX)
        (Or.inr (by have := fragCells_ge AX (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AOFF)
        (Or.inr (by have := fragCells_ge AOFF (by simp [fragCells]); omega))]
    exact hsubcL
  · -- ADST preserved
    have hAD : loadWord S₈.memory ADST = loadWord S.memory ADST := by
      apply loadWord_congr
      intro b hb1 hb2
      have hreg : b < dst + 32 * i ∨ dst + 32 * i + 32 ≤ b := by
        have := fragCells_ge ADST (by simp [fragCells]); omega
      have hcells : ∀ cc ∈ addRoundCells, b < cc ∨ cc + 32 ≤ b := by
        intro cc hcc
        rcases cells_disj (addRoundCells_cells hcc)
            (show ADST ∈ fragCells by simp [fragCells])
            (addRoundCells_neADST hcc) with h | h
        · omega
        · omega
      exact hmemEq b hreg hcells
    rw [hAD]; exact hADST
  · -- ASRC preserved
    have hAS : loadWord S₈.memory ASRC = loadWord S.memory ASRC := by
      apply loadWord_congr
      intro b hb1 hb2
      have hreg : b < dst + 32 * i ∨ dst + 32 * i + 32 ≤ b := by
        have := fragCells_ge ASRC (by simp [fragCells]); omega
      have hcells : ∀ cc ∈ addRoundCells, b < cc ∨ cc + 32 ≤ b := by
        intro cc hcc
        rcases cells_disj (addRoundCells_cells hcc)
            (show ASRC ∈ fragCells by simp [fragCells])
            (addRoundCells_neASRC hcc) with h | h
        · omega
        · omega
      exact hmemEq b hreg hcells
    rw [hAS]; exact hASRC
  · -- activeWords unchanged
    rfl
  · -- env unchanged
    rfl

/-! ## The subtraction pass -/

/-- The wrapped difference of two `ofNat` words. -/
theorem toNat_sub_ofNat (x y : Nat) (hx : x < 2 ^ 256) (hy : y < 2 ^ 256) :
    (BitVec.ofNat 256 x - BitVec.ofNat 256 y).toNat =
      if x < y then 2 ^ 256 + x - y else x - y := by
  rw [toNat_sub_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hy, sub_wrap x y hx]

/-- One round of the subtraction pass: reads `dst[i]` (the wrapped sum limb,
through the `ADST` cell) and `MOD[i]` (at address `32·i`), writes the
conditional-subtraction limb into `SUBC` and the new borrow, and increments
`I2`. -/
theorem subRound_steps [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (suml ms subc₀ : List Nat) (n i : Nat)
    (cand : List Nat) (b c1 : Nat) {M₀ : Nat → UInt8}
    {k : List Asm} {σ : List AVal} {S : EvmState}
    (hSub : findLabel l.lSub prog = some (amSubBody l ++ k))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hi : i < n) (hn32 : n ≤ 32)
    (hdstN : dst + 32 * n ≤ Ncell)
    (hsubcDst : dst + 32 * n ≤ SUBC)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = i)
    (hle : b ≤ 1)
    (hC2 : (loadWord S.memory C2).toNat = b)
    (hC1 : (loadWord S.memory C1).toNat = c1)
    (hADST : loadWord S.memory ADST = BitVec.ofNat 256 dst)
    (hdef : subDigitLists (suml.take i) (ms.take i) 0 = (cand, b))
    (hdstL : yLimbs S.memory dst n = suml)
    (hmodL : yLimbs S.memory MOD n = ms)
    (hsubcL : yLimbs S.memory SUBC n = cand ++ subc₀.drop i)
    (hsumlen : suml.length = n) (hmslen : ms.length = n) (hsubc0len : subc₀.length = n)
    (hsd : lget suml i < radix) (hmd : lget ms i < radix)
    (hkeeps : AddModKeeps S.memory M₀ dst n) :
    ∃ S', ASteps prog ⟨amSubBody l ++ k, σ, S⟩
        ⟨amSubBody l ++ k, σ, S'⟩ ∧
      (loadWord S'.memory I2).toNat = i + 1 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      (loadWord S'.memory C2).toNat = (subDigitLists (suml.take (i + 1)) (ms.take (i + 1)) 0).2 ∧
      (subDigitLists (suml.take (i + 1)) (ms.take (i + 1)) 0).2 ≤ 1 ∧
      (loadWord S'.memory C1).toNat = c1 ∧
      yLimbs S'.memory SUBC n =
        (subDigitLists (suml.take (i + 1)) (ms.take (i + 1)) 0).1 ++ subc₀.drop (i + 1) ∧
      yLimbs S'.memory dst n = suml ∧
      yLimbs S'.memory MOD n = ms ∧
      AddModKeeps S'.memory M₀ dst n ∧
      loadWord S'.memory ADST = BitVec.ofNat 256 dst ∧
      S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hr : radix = 2 ^ 256 := rfl
  have hrpos : 0 < radix := radix_pos
  have hncell : Ncell = 0x1cc0 := rfl
  have hI2c : I2 = 0x1e60 := rfl
  have hAOFFc : AOFF = 0x1e80 := rfl
  have hAXc : AX = 0x1ea0 := rfl
  have hAYc : AY = 0x1ec0 := rfl
  have hASc : AS = 0x1ee0 := rfl
  have hAZc : AZ = 0x1f00 := rfl
  have hC1c : C1 = 0x1d40 := rfl
  have hC2c : C2 = 0x1d60 := rfl
  have hADSTc : ADST = 0x1e20 := rfl
  have hsubcEq : SUBC = 0x1400 := rfl
  have hmod0 : (MOD : Nat) = 0 := rfl
  have hnclt : (0x1cc0 : Nat) < 2 ^ 256 := by decide
  have hi256 : i < 2 ^ 256 := by omega
  have hsumlen' : i < suml.length := by omega
  have hmslen' : i < ms.length := by omega
  have hsubc0len' : i < subc₀.length := by omega
  have htakelen : (suml.take i).length = i := by rw [List.length_take]; omega
  have htakelenY : (ms.take i).length = i := by rw [List.length_take]; omega
  have hcandlen : cand.length = i := by
    have h := length_subDigitLists_left (xs := suml.take i) (ys := ms.take i)
      (borrow := 0) (by simp [htakelen, htakelenY])
    rw [hdef] at h
    have h2 : cand.length = (suml.take i).length := by simpa using h
    rwa [htakelen] at h2
  -- the eight states of one round
  set S₁ : EvmState := {S with memory :=
    (storeWord S.memory AOFF (BitVec.ofNat 256 (32 * i)))} with hS₁def
  set S₂ : EvmState := {S₁ with memory :=
    (storeWord S₁.memory AX (BitVec.ofNat 256 (lget suml i)))} with hS₂def
  set S₃ : EvmState := {S₂ with memory :=
    (storeWord S₂.memory AY (BitVec.ofNat 256 (lget ms i)))} with hS₃def
  set S₄ : EvmState := {S₃ with memory :=
    (storeWord S₃.memory AS
      (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)))} with hS₄def
  set S₅ : EvmState := {S₄ with memory :=
    (storeWord S₄.memory AZ ((BitVec.ofNat 256 (lget suml i) -
      BitVec.ofNat 256 (lget ms i)) - BitVec.ofNat 256 b))} with hS₅def
  set S₆ : EvmState := {S₅ with memory :=
    (storeWord S₅.memory C2
      (BitVec.ofNat 256 (if lget suml i < lget ms i + b then 1 else 0)))} with hS₆def
  set S₇ : EvmState := {S₆ with memory :=
    (storeWord S₆.memory (SUBC + 32 * i)
      ((BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
        BitVec.ofNat 256 b))} with hS₇def
  set S₈ : EvmState := {S₇ with memory :=
    (storeWord S₇.memory I2 (BitVec.ofNat 256 (i + 1)))} with hS₈def
  have hS₁mem : S₁.memory =
      storeWord S.memory AOFF (BitVec.ofNat 256 (32 * i)) := rfl
  have hS₂mem : S₂.memory =
      storeWord S₁.memory AX (BitVec.ofNat 256 (lget suml i)) := rfl
  have hS₃mem : S₃.memory =
      storeWord S₂.memory AY (BitVec.ofNat 256 (lget ms i)) := rfl
  have hS₄mem : S₄.memory =
      storeWord S₃.memory AS
        (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) := rfl
  have hS₅mem : S₅.memory =
      storeWord S₄.memory AZ ((BitVec.ofNat 256 (lget suml i) -
        BitVec.ofNat 256 (lget ms i)) - BitVec.ofNat 256 b) := rfl
  have hS₆mem : S₆.memory =
      storeWord S₅.memory C2
        (BitVec.ofNat 256 (if lget suml i < lget ms i + b then 1 else 0)) := rfl
  have hS₇mem : S₇.memory =
      storeWord S₆.memory (SUBC + 32 * i)
        ((BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
          BitVec.ofNat 256 b) := rfl
  have hS₈mem : S₈.memory =
      storeWord S₇.memory I2 (BitVec.ofNat 256 (i + 1)) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := haw
  have hawS₃ : 0x1f40 ≤ 32 * S₃.activeWords.toNat := haw
  have hawS₄ : 0x1f40 ≤ 32 * S₄.activeWords.toNat := haw
  have hawS₅ : 0x1f40 ≤ 32 * S₅.activeWords.toNat := haw
  have hawS₆ : 0x1f40 ≤ 32 * S₆.activeWords.toNat := haw
  have hawS₇ : 0x1f40 ≤ 32 * S₇.activeWords.toNat := haw
  have hawS₈ : 0x1f40 ≤ 32 * S₈.activeWords.toNat := haw
  -- word values and limb reads
  have hI2w : loadWord S.memory I2 = BitVec.ofNat 256 i := word_of_toNat hI2 hi256
  have hC2w : loadWord S.memory C2 = BitVec.ofNat 256 b := word_of_toNat hC2 (by omega)
  have hxL : (loadWord S.memory (dst + 32 * i)).toNat = lget suml i :=
    yLimb_lget hi hdstL (by omega)
  have hxw : loadWord S.memory (dst + 32 * i) = BitVec.ofNat 256 (lget suml i) :=
    word_of_toNat hxL (by omega)
  have hyL : (loadWord S.memory (32 * i)).toNat = lget ms i := by
    have h1 : (loadWord S.memory (MOD + 32 * i)).toNat = lget ms i :=
      yLimb_lget hi hmodL (by omega)
    have h2 : (MOD + 32 * i : Nat) = 32 * i := by
      rw [show (MOD : Nat) = 0 from rfl, Nat.zero_add]
    rw [h2] at h1
    exact h1
  have hyw : loadWord S.memory (32 * i) = BitVec.ofNat 256 (lget ms i) :=
    word_of_toNat hyL (by omega)
  have hdsti : dst + 32 * i < 2 ^ 256 := by omega
  have h32i : 32 * i < 2 ^ 256 := by omega
  have hsubci : SUBC + 32 * i < 2 ^ 256 := by omega
  -- the borrow recurrence
  have hsb := subLimbBits hsd hmd hle
  simp only [] at hsb
  rw [hr] at hsb
  have hble : (if lget suml i < lget ms i + b then 1 else 0) ≤ 1 := by split <;> omega
  have hdifflt : (if lget suml i < lget ms i then 2 ^ 256 + lget suml i - lget ms i
      else lget suml i - lget ms i) < 2 ^ 256 := by split <;> omega
  -- per-state value facts
  have hAOFF1 : loadWord S₁.memory AOFF = BitVec.ofNat 256 (32 * i) := by
    rw [hS₁mem]; exact loadWord_storeWord _ _ _
  have hdisjdst : loadWord S₁.memory (dst + 32 * i) =
      loadWord S.memory (dst + 32 * i) := by
    rw [hS₁mem]
    exact loadWord_storeWord_disj (p := AOFF) (q := dst + 32 * i) (by omega)
  have hdisjmod : loadWord S₁.memory (32 * i) = loadWord S.memory (32 * i) := by
    rw [hS₁mem]
    exact loadWord_storeWord_disj (p := AOFF) (q := 32 * i) (by omega)
  have hADST1 : loadWord S₁.memory ADST = BitVec.ofNat 256 dst := by
    rw [hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hADST
  have hAXval : evalExpr (loadAt (.bin .add (.load ADST) (.load AOFF))) S₁
      = BitVec.ofNat 256 (lget suml i) := by
    rw [eval_mload_addCells hADST1 hAOFF1 hdsti, hdisjdst, hxw]
  have hAXaddrN : (evalExpr (.bin .add (.load ADST) (.load AOFF)) S₁).toNat
      = dst + 32 * i := by
    rw [eval_add_loads S₁ ADST AOFF dst (32 * i) hADST1 hAOFF1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hdsti]
  have hAOFF2 : loadWord S₂.memory AOFF = BitVec.ofNat 256 (32 * i) := by
    rw [hS₂mem, loadWord_storeWord_disj (p := AX) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAOFF1
  have hAYtn : (loadWord S₂.memory (32 * i)).toNat = lget ms i := by
    rw [hS₂mem, loadWord_storeWord_disj (p := AX) (q := 32 * i) (by omega), hdisjmod]
    exact hyL
  have hAYval : evalExpr (loadAt (.load AOFF)) S₂ = BitVec.ofNat 256 (lget ms i) := by
    show loadWord S₂.memory (evalExpr (.load AOFF) S₂).toNat = _
    rw [show evalExpr (.load AOFF) S₂ = BitVec.ofNat 256 (32 * i) from hAOFF2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32i]
    exact word_of_toNat hAYtn (by omega)
  have hAYaddrN : (evalExpr (.load AOFF) S₂).toNat = 32 * i := by
    rw [show evalExpr (.load AOFF) S₂ = BitVec.ofNat 256 (32 * i) from hAOFF2,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt h32i]
  have hAX3 : loadWord S₃.memory AX = BitVec.ofNat 256 (lget suml i) := by
    rw [hS₃mem, loadWord_storeWord_disj (p := AY) (q := AX) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hS₂mem]
    exact loadWord_storeWord _ _ _
  have hAY3 : loadWord S₃.memory AY = BitVec.ofNat 256 (lget ms i) := by
    rw [hS₃mem]; exact loadWord_storeWord _ _ _
  have hAS4 : loadWord S₄.memory AS =
      BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i) := by
    rw [hS₄mem]; exact loadWord_storeWord _ _ _
  have hAS4tn : (loadWord S₄.memory AS).toNat =
      if lget suml i < lget ms i then 2 ^ 256 + lget suml i - lget ms i
        else lget suml i - lget ms i := by
    rw [hAS4, toNat_sub_ofNat _ _ (by omega) (by omega)]
  have hC2_4 : loadWord S₄.memory C2 = BitVec.ofNat 256 b := by
    rw [hS₄mem, loadWord_storeWord_disj (p := AS) (q := C2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := C2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := AX) (q := C2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := C2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hC2w
  have hAS5 : loadWord S₅.memory AS =
      BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i) := by
    rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AS) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hS₄mem]
    exact loadWord_storeWord _ _ _
  have hAX5 : loadWord S₅.memory AX = BitVec.ofNat 256 (lget suml i) := by
    rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AX) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := AX) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAX3
  have hAY5 : loadWord S₅.memory AY = BitVec.ofNat 256 (lget ms i) := by
    rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AY) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := AY) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAY3
  have hAZ5 : loadWord S₅.memory AZ =
      (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
        BitVec.ofNat 256 b := by
    rw [hS₅mem]; exact loadWord_storeWord _ _ _
  have hC2_5 : (loadWord S₅.memory C2).toNat = b := by
    rw [show loadWord S₅.memory C2 = BitVec.ofNat 256 b from by
      rw [hS₅mem, loadWord_storeWord_disj (p := AZ) (q := C2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hC2_4],
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAS5tn : (loadWord S₅.memory AS).toNat =
      if lget suml i < lget ms i then 2 ^ 256 + lget suml i - lget ms i
        else lget suml i - lget ms i := by
    rw [hAS5, toNat_sub_ofNat _ _ (by omega) (by omega)]
  have hAX5tn : (loadWord S₅.memory AX).toNat = lget suml i := by
    rw [hAX5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAY5tn : (loadWord S₅.memory AY).toNat = lget ms i := by
    rw [hAY5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hAZ5tn : (loadWord S₅.memory AZ).toNat =
      lget suml i + 2 ^ 256 * (if lget suml i < lget ms i + b then 1 else 0) -
        lget ms i - b := by
    rw [hAZ5, toNat_sub_eq, toNat_sub_ofNat (lget suml i) (lget ms i) (by omega) (by omega),
      show (BitVec.ofNat 256 b).toNat = b from by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
      sub_wrap _ _ hdifflt, hsb.1]
  have hAZvalTN : ((BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
      BitVec.ofNat 256 b).toNat =
      lget suml i + radix * (if lget suml i < lget ms i + b then 1 else 0) -
        lget ms i - b := by
    have h2 := hAZ5tn
    rw [hAZ5] at h2
    exact h2
  have hC2val : evalExpr
        (.bin .or (.bin .lt (.load AX) (.load AY)) (.bin .lt (.load AS) (.load C2))) S₅
      = BitVec.ofNat 256 (if lget suml i < lget ms i + b then 1 else 0) := by
    apply word_of_toNat
    · have h1 : (evalExpr
          (.bin .or (.bin .lt (.load AX) (.load AY))
            (.bin .lt (.load AS) (.load C2))) S₅).toNat =
          ((if lget suml i < lget ms i then 1 else 0) |||
            (if (if lget suml i < lget ms i then 2 ^ 256 + lget suml i - lget ms i
                  else lget suml i - lget ms i) < b then 1 else 0)) := by
        simp only [evalExpr, evalBin, toNat_or_eq, toNat_b2w_eq,
          BitVec.ult_iff_toNat_lt]
        rw [hAX5tn, hAY5tn, hAS5tn, hC2_5]
      rw [h1, ← hsb.2]
    · omega
  have hAOFF6 : loadWord S₆.memory AOFF = BitVec.ofNat 256 (32 * i) := by
    rw [hS₆mem, loadWord_storeWord_disj (p := C2) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₅mem, loadWord_storeWord_disj (p := AZ) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := AOFF) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hAOFF2
  have hAZ6 : loadWord S₆.memory AZ =
      (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
        BitVec.ofNat 256 b := by
    rw [hS₆mem, loadWord_storeWord_disj (p := C2) (q := AZ) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)), hAZ5]
  have hAZval6 : evalExpr (Expr.load AZ) S₆ =
      (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
        BitVec.ofNat 256 b := by
    show loadWord S₆.memory AZ = _
    rw [hAZ6]
  have hI2₇ : loadWord S₇.memory I2 = BitVec.ofNat 256 i := by
    rw [hS₇mem, loadWord_storeWord_disj (p := SUBC + 32 * i) (q := I2) (by omega),
      hS₆mem, loadWord_storeWord_disj (p := C2) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₅mem, loadWord_storeWord_disj (p := AZ) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := AX) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := I2) (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hI2w
  -- the straight-line chain
  have hsteps : ASteps prog ⟨amSubBody l ++ k, σ, S⟩
      ⟨amSubBody l ++ k, σ, S₈⟩ := by
    rw [amSubBody_eq l k]
    refine (exitTest_fall (prog := prog) haw hN hI2 (by omega) hi).trans ?_
    refine (store_off32_steps (prog := prog) haw hI2w).trans ?_
    refine (store_cell_val (prog := prog) (c := AX)
      (e := loadAt (.bin .add (.load ADST) (.load AOFF))) (w := BitVec.ofNat 256 (lget suml i))
      hAXval ⟨(by
        rw [hAXaddrN]
        show dst + 32 * i + 32 ≤ 32 * S₁.activeWords.toNat
        omega),
        ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
          exprOK_load_cell haw (by simp [fragCells])⟩⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := AY)
      (e := loadAt (.load AOFF)) (w := BitVec.ofNat 256 (lget ms i))
      hAYval ⟨(by
        rw [hAYaddrN]
        show 32 * i + 32 ≤ 32 * S₂.activeWords.toNat
        omega),
        exprOK_load_cell haw (by simp [fragCells])⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := AS) (e := .bin .sub (.load AX) (.load AY))
      (w := BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i))
      (eval_sub_loads S₃ AX AY _ _ hAX3 hAY3)
      ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := AZ) (e := .bin .sub (.load AS) (.load C2))
      (w := (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
        BitVec.ofNat 256 b)
      (eval_sub_loads S₄ AS C2 _ _ hAS4 hC2_4)
      ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (store_cell_val (prog := prog) (c := C2)
      (e := .bin .or (.bin .lt (.load AX) (.load AY)) (.bin .lt (.load AS) (.load C2)))
      (w := BitVec.ofNat 256 (if lget suml i < lget ms i + b then 1 else 0)) hC2val
      ⟨rfl, ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        exprOK_load_cell haw (by simp [fragCells])⟩,
        ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
          exprOK_load_cell haw (by simp [fragCells])⟩⟩
      (cell_pinned haw (by simp [fragCells]))).trans ?_
    refine (storeAt_val (prog := prog)
      (addrE := .bin .add (.imm SUBC) (.load AOFF)) (valE := .load AZ)
      (addr := SUBC + 32 * i)
      (w := (BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
        BitVec.ofNat 256 b)
      (eval_addr_add hAOFF6) hAZval6 hsubci
      (exprOK_load_cell haw (by simp [fragCells]))
      ⟨rfl, True.intro, exprOK_load_cell haw (by simp [fragCells])⟩
      (by show SUBC + 32 * i + 32 ≤ 32 * S₆.activeWords.toNat; omega)).trans ?_
    refine (incr_I2_steps (prog := prog) (yst := S₇) haw hI2₇ hi256).trans ?_
    exact ASteps.single (astep_jump hSub)
  -- the one-step list recurrence
  have hsp : subDigitLists (suml.take (i + 1)) (ms.take (i + 1)) 0 =
      (cand ++ [lget suml i + radix * (if lget suml i < lget ms i + b then 1 else 0) -
          lget ms i - b],
        if lget suml i < lget ms i + b then 1 else 0) := by
    rw [List.take_add_one, List.take_add_one,
      List.getElem?_eq_getElem hsumlen', List.getElem?_eq_getElem hmslen',
      Option.toList_some, Option.toList_some,
      subDigitLists_append_single (by simp [htakelen, htakelenY]), hdef,
      lget_eq hsumlen', lget_eq hmslen']
  have hsp1 : (subDigitLists (suml.take (i + 1)) (ms.take (i + 1)) 0).1 =
      cand ++ [lget suml i + radix * (if lget suml i < lget ms i + b then 1 else 0) -
        lget ms i - b] := congrArg Prod.fst hsp
  have hsp2 : (subDigitLists (suml.take (i + 1)) (ms.take (i + 1)) 0).2 =
      (if lget suml i < lget ms i + b then 1 else 0) := congrArg Prod.snd hsp
  -- byte-level: the round writes only scratch cells and limb i of SUBC
  have hmemEq : ∀ a, (a < SUBC + 32 * i ∨ SUBC + 32 * i + 32 ≤ a) →
      (∀ cc ∈ addRoundCells, a < cc ∨ cc + 32 ≤ a) → S₈.memory a = S.memory a := by
    intro a ha hall
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    rw [storeWord_other (hall I2 (by simp [addRoundCells])),
      storeWord_other (p := SUBC + 32 * i) ha,
      storeWord_other (hall C2 (by simp [addRoundCells])),
      storeWord_other (hall AZ (by simp [addRoundCells])),
      storeWord_other (hall AS (by simp [addRoundCells])),
      storeWord_other (hall AY (by simp [addRoundCells])),
      storeWord_other (hall AX (by simp [addRoundCells])),
      storeWord_other (hall AOFF (by simp [addRoundCells]))]
  have hsubcReg : SUBC ≤ SUBC + 32 * i ∧ SUBC + 32 * i + 32 ≤ SUBC + 32 * n := by omega
  have hmI2 : I2 ∈ addModScratch := by decide
  have hmC1 : C1 ∈ addModScratch := by decide
  have hmC2 : C2 ∈ addModScratch := by decide
  have hmAZ : AZ ∈ addModScratch := by decide
  have hmAS : AS ∈ addModScratch := by decide
  have hmAY : AY ∈ addModScratch := by decide
  have hmAX : AX ∈ addModScratch := by decide
  have hmAOFF : AOFF ∈ addModScratch := by decide
  -- the exit-state properties
  refine ⟨S₈, hsteps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- I2
    rw [hS₈mem, loadWord_storeWord, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · -- Ncell
    have hNc : loadWord S₈.memory Ncell = loadWord S.memory Ncell := by
      apply loadWord_congr
      intro b hb1 hb2
      have hreg : b < SUBC + 32 * i ∨ SUBC + 32 * i + 32 ≤ b := by
        right
        have := fragCells_ge Ncell (by simp [fragCells])
        omega
      have hcells : ∀ cc ∈ addRoundCells, b < cc ∨ cc + 32 ≤ b := by
        intro cc hcc
        have hge := addRoundCells_ge hcc
        rcases cells_disj (addRoundCells_cells hcc)
            (show Ncell ∈ fragCells by simp [fragCells])
            (addRoundCells_ne hcc) with h | h
        · omega
        · omega
      exact hmemEq b hreg hcells
    rw [hNc]; exact hN
  · -- C2
    rw [hS₈mem, loadWord_storeWord_disj (p := I2) (q := C2)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₇mem, loadWord_storeWord_disj (p := SUBC + 32 * i) (q := C2) (by omega),
      hS₆mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), hsp]
  · -- borrow bound
    rw [hsp]; exact hble
  · -- C1 preserved (chain over the round's writes, none touching C1)
    rw [hS₈mem, loadWord_storeWord_disj (p := I2) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₇mem, loadWord_storeWord_disj (p := SUBC + 32 * i) (q := C1) (by omega),
      hS₆mem, loadWord_storeWord_disj (p := C2) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₅mem, loadWord_storeWord_disj (p := AZ) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₄mem, loadWord_storeWord_disj (p := AS) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₃mem, loadWord_storeWord_disj (p := AY) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₂mem, loadWord_storeWord_disj (p := AX) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      hS₁mem, loadWord_storeWord_disj (p := AOFF) (q := C1)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hC1
  · -- SUBC limbs
    have hset : yLimbs S₈.memory SUBC n =
        cand ++ [lget suml i + radix * (if lget suml i < lget ms i + b then 1 else 0) -
          lget ms i - b] ++ subc₀.drop (i + 1) := by
      rw [hS₈mem, yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₇mem,
        yLimbs_storeWord S₆.memory SUBC n i hi
          ((BitVec.ofNat 256 (lget suml i) - BitVec.ofNat 256 (lget ms i)) -
            BitVec.ofNat 256 b),
        hAZvalTN,
        hS₆mem, yLimbs_storeWord_disjoint (q := C2)
          (Or.inr (by have := fragCells_ge C2 (by simp [fragCells]); omega)),
        hS₅mem, yLimbs_storeWord_disjoint (q := AZ)
          (Or.inr (by have := fragCells_ge AZ (by simp [fragCells]); omega)),
        hS₄mem, yLimbs_storeWord_disjoint (q := AS)
          (Or.inr (by have := fragCells_ge AS (by simp [fragCells]); omega)),
        hS₃mem, yLimbs_storeWord_disjoint (q := AY)
          (Or.inr (by have := fragCells_ge AY (by simp [fragCells]); omega)),
        hS₂mem, yLimbs_storeWord_disjoint (q := AX)
          (Or.inr (by have := fragCells_ge AX (by simp [fragCells]); omega)),
        hS₁mem, yLimbs_storeWord_disjoint (q := AOFF)
          (Or.inr (by have := fragCells_ge AOFF (by simp [fragCells]); omega)),
        hsubcL, drop_cons_of_lt subc₀ i hsubc0len', set_append_mid' hcandlen]
      simp
    rw [hset, hsp1]
  · -- dst limbs preserved
    have hmodSubc : dst + 32 * n ≤ SUBC + 32 * i := by omega
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    rw [yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := SUBC + 32 * i) (Or.inr hmodSubc),
      yLimbs_storeWord_disjoint (q := C2)
        (Or.inr (by have := fragCells_ge C2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AZ)
        (Or.inr (by have := fragCells_ge AZ (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AS)
        (Or.inr (by have := fragCells_ge AS (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AY)
        (Or.inr (by have := fragCells_ge AY (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AX)
        (Or.inr (by have := fragCells_ge AX (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AOFF)
        (Or.inr (by have := fragCells_ge AOFF (by simp [fragCells]); omega))]
    exact hdstL
  · -- MOD limbs preserved
    have hmodSubc : MOD + 32 * n ≤ SUBC + 32 * i := by omega
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    rw [yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := SUBC + 32 * i) (Or.inr hmodSubc),
      yLimbs_storeWord_disjoint (q := C2)
        (Or.inr (by have := fragCells_ge C2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AZ)
        (Or.inr (by have := fragCells_ge AZ (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AS)
        (Or.inr (by have := fragCells_ge AS (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AY)
        (Or.inr (by have := fragCells_ge AY (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AX)
        (Or.inr (by have := fragCells_ge AX (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := AOFF)
        (Or.inr (by have := fragCells_ge AOFF (by simp [fragCells]); omega))]
    exact hmodL
  · -- keeps
    rw [hS₈mem, hS₇mem, hS₆mem, hS₅mem, hS₄mem, hS₃mem, hS₂mem, hS₁mem]
    exact keeps_storeWord_cell
      (keeps_storeWord_subc
        (keeps_storeWord_cell
          (keeps_storeWord_cell
            (keeps_storeWord_cell
              (keeps_storeWord_cell
                (keeps_storeWord_cell
                  (keeps_storeWord_cell hkeeps hmAOFF) hmAX) hmAY) hmAS) hmAZ) hmC2)
        hsubcReg) hmI2
  · -- ADST preserved
    have hAD : loadWord S₈.memory ADST = loadWord S.memory ADST := by
      apply loadWord_congr
      intro b hb1 hb2
      have hreg : b < SUBC + 32 * i ∨ SUBC + 32 * i + 32 ≤ b := by
        right
        have := fragCells_ge ADST (by simp [fragCells])
        omega
      have hcells : ∀ cc ∈ addRoundCells, b < cc ∨ cc + 32 ≤ b := by
        intro cc hcc
        rcases cells_disj (addRoundCells_cells hcc)
            (show ADST ∈ fragCells by simp [fragCells])
            (addRoundCells_neADST hcc) with h | h
        · omega
        · omega
      exact hmemEq b hreg hcells
    rw [hAD]; exact hADST
  · -- activeWords unchanged
    rfl
  · -- env unchanged
    rfl

/-! ## The passes -/

/-- The full addition pass: from the loop top to the `lSubStart` target. -/
theorem addPass_steps [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (xs ys subc₀ : List Nat) (n : Nat)
    {cont : List Asm} {σ : List AVal} {S : EvmState} {M₀ : Nat → UInt8}
    (hAdd : findLabel l.lAdd prog =
      some (amAddBody l ++ amFromSubStart l ++ cont))
    (hSubStart : findLabel l.lSubStart prog =
      some (store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hdstN : dst + 32 * n ≤ Ncell) (hsrcN : src + 32 * n ≤ Ncell)
    (hsubcDst : dst + 32 * n ≤ SUBC)
    (hds : src + 32 * n ≤ dst ∨ dst + 32 * n ≤ src ∨ src = dst)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = 0)
    (hC1 : (loadWord S.memory C1).toNat = 0)
    (hADST : loadWord S.memory ADST = BitVec.ofNat 256 dst)
    (hASRC : loadWord S.memory ASRC = BitVec.ofNat 256 src)
    (hxL : yLimbs S.memory dst n = xs)
    (hyL : yLimbs S.memory src n = ys)
    (hxlen : xs.length = n) (hylen : ys.length = n)
    (hxd : ∀ d ∈ xs, d < radix) (hyd : ∀ d ∈ ys, d < radix)
    (hsubcL : yLimbs S.memory SUBC n = subc₀)
    (hkeeps : AddModKeeps S.memory M₀ dst n) :
    ∃ S', ASteps prog
        ⟨amAddBody l ++ amFromSubStart l ++ cont, σ, S⟩
        ⟨store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont, σ, S'⟩ ∧
      yLimbs S'.memory dst n = (addDigitLists xs ys 0).1 ∧
      (loadWord S'.memory C1).toNat = (addDigitLists xs ys 0).2 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      AddModKeeps S'.memory M₀ dst n ∧
      yLimbs S'.memory SUBC n = subc₀ ∧
      loadWord S'.memory ADST = BitVec.ofNat 256 dst ∧
      loadWord S'.memory ASRC = BitVec.ofNat 256 src ∧
      S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hyLread : ∀ j, 0 ≤ j → j < n →
      (loadWord S.memory (src + 32 * j)).toNat = lget ys j :=
    fun j _ hj => yLimb_lget hj hyL (by omega)
  have hround : ∀ {m : Nat} {St : EvmState}, 0 < m →
      (∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        (loadWord St.memory C1).toNat = (addDigitLists (xs.take i) (ys.take i) 0).2 ∧
        (addDigitLists (xs.take i) (ys.take i) 0).2 ≤ 1 ∧
        yLimbs St.memory dst n = (addDigitLists (xs.take i) (ys.take i) 0).1 ++ xs.drop i ∧
        (∀ j, i ≤ j → j < n →
          (loadWord St.memory (src + 32 * j)).toNat = lget ys j) ∧
        AddModKeeps St.memory M₀ dst n ∧
        yLimbs St.memory SUBC n = subc₀ ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        loadWord St.memory ASRC = BitVec.ofNat 256 src ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) →
      ((∃ St', (∃ i, (loadWord St'.memory I2).toNat = i ∧ i + (m - 1) = n ∧
        (loadWord St'.memory Ncell).toNat = n ∧
        (loadWord St'.memory C1).toNat = (addDigitLists (xs.take i) (ys.take i) 0).2 ∧
        (addDigitLists (xs.take i) (ys.take i) 0).2 ≤ 1 ∧
        yLimbs St'.memory dst n = (addDigitLists (xs.take i) (ys.take i) 0).1 ++ xs.drop i ∧
        (∀ j, i ≤ j → j < n →
          (loadWord St'.memory (src + 32 * j)).toNat = lget ys j) ∧
        AddModKeeps St'.memory M₀ dst n ∧
        yLimbs St'.memory SUBC n = subc₀ ∧
        loadWord St'.memory ADST = BitVec.ofNat 256 dst ∧
        loadWord St'.memory ASRC = BitVec.ofNat 256 src ∧
        St'.activeWords = S.activeWords ∧
          St'.env = S.env) ∧
        ASteps prog ⟨amAddBody l ++ amFromSubStart l ++ cont, σ, St⟩
          ⟨amAddBody l ++ amFromSubStart l ++ cont, σ, St'⟩) ∨
      ((yLimbs St.memory dst n = (addDigitLists xs ys 0).1 ∧
        (loadWord St.memory C1).toNat = (addDigitLists xs ys 0).2 ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        yLimbs St.memory SUBC n = subc₀ ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        loadWord St.memory ASRC = BitVec.ofNat 256 src ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) ∧
        ASteps prog ⟨amAddBody l ++ amFromSubStart l ++ cont, σ, St⟩
          ⟨store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont, σ, St⟩)) := by
    intro m St _hmpos hm
    rcases hm with ⟨i, hI2i, him, hNst, hC1st, hcle, hdstst, hsrcreadst, hkeepsst,
      hsubcst, hADSTst, hASRCst, hawEq, henvEq⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- exit (unreachable: 0 < m)
      exact absurd hm0 (by omega)
    · -- iterate round
      left
      have hin : i < n := by omega
      have hxd' : lget xs i < radix := by
        have himem : xs[i]'(show i < xs.length by omega) ∈ xs :=
          mem_getElem (show i < xs.length by omega)
        rw [lget_eq (show i < xs.length by omega)]
        exact hxd _ himem
      have hyd' : lget ys i < radix := by
        have himem : ys[i]'(show i < ys.length by omega) ∈ ys :=
          mem_getElem (show i < ys.length by omega)
        rw [lget_eq (show i < ys.length by omega)]
        exact hyd _ himem
      have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by rw [hawEq]; exact haw
      obtain ⟨S', hsteps, hI2', hN', hC1', hcle', hdst', hsrc', hkeeps', hsubc',
        hADST', hASRC', hawEq', henvEq'⟩ :=
        addRound_steps (dst := dst) (src := src) (l := l) (xs := xs) (ys := ys)
          (n := n) (i := i)
          (addDigitLists (xs.take i) (ys.take i) 0).1
          (addDigitLists (xs.take i) (ys.take i) 0).2
          (k := amFromSubStart l ++ cont) hAdd hawSt hin hn32 hdstN hsrcN
          hsubcDst hds hNst
          hI2i hcle hC1st hADSTst hASRCst rfl hdstst hxlen hylen hxd' hyd' hsrcreadst
          hsubcst hkeepsst
      have hawEq'' : S'.activeWords = S.activeWords := by rw [hawEq', hawEq]
      have henvEq'' : S'.env = S.env := by rw [henvEq']; exact henvEq
      exact ⟨S', ⟨i + 1, hI2', by omega, hN', hC1', hcle', hdst', hsrc', hkeeps',
        hsubc', hADST', hASRC', hawEq'', henvEq''⟩, hsteps⟩
  have hexit : ∀ (St : EvmState),
      (∃ i, (loadWord St.memory I2).toNat = i ∧ i + 0 = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        (loadWord St.memory C1).toNat = (addDigitLists (xs.take i) (ys.take i) 0).2 ∧
        (addDigitLists (xs.take i) (ys.take i) 0).2 ≤ 1 ∧
        yLimbs St.memory dst n = (addDigitLists (xs.take i) (ys.take i) 0).1 ++ xs.drop i ∧
        (∀ j, i ≤ j → j < n →
          (loadWord St.memory (src + 32 * j)).toNat = lget ys j) ∧
        AddModKeeps St.memory M₀ dst n ∧
        yLimbs St.memory SUBC n = subc₀ ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        loadWord St.memory ASRC = BitVec.ofNat 256 src ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) →
      ((yLimbs St.memory dst n = (addDigitLists xs ys 0).1 ∧
        (loadWord St.memory C1).toNat = (addDigitLists xs ys 0).2 ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        yLimbs St.memory SUBC n = subc₀ ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        loadWord St.memory ASRC = BitVec.ofNat 256 src ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) ∧
        ASteps prog ⟨amAddBody l ++ amFromSubStart l ++ cont, σ, St⟩
          ⟨store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont, σ, St⟩) := by
    intro St hm
    rcases hm with ⟨i, hI2i, him, hNst, hC1st, -, hdstst, -, hkeepsst, hsubcst,
      hADSTst, hASRCst, hawEq, henvEq⟩
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by rw [hawEq]; exact haw
    have hin : i = n := by omega
    refine ⟨⟨?_, ?_, hNst, hkeepsst, hsubcst, hADSTst, hASRCst, hawEq, henvEq⟩, ?_⟩
    · rw [hdstst, hin]
      have h1 : xs.take n = xs := take_eq_of_length xs n (by omega)
      have h2 : ys.take n = ys := take_eq_of_length ys n (by omega)
      have h3 : xs.drop n = [] := drop_eq_nil_of_length xs n (by omega)
      simp [h1, h2, h3]
    · rw [hC1st, hin]
      have h1 : xs.take n = xs := take_eq_of_length xs n (by omega)
      have h2 : ys.take n = ys := take_eq_of_length ys n (by omega)
      simp [h1, h2]
    · exact exitTest_taken (prog := prog) hawSt hNst hI2i (by omega) (by omega) hSubStart
  obtain ⟨S', hP, hsteps⟩ :=
    loop_counted (model := model) (prog := prog)
      (top := amAddBody l ++ amFromSubStart l ++ cont)
      (σ := σ)
      (c' := store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont)
      (Inv := fun St m =>
        ∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
          (loadWord St.memory Ncell).toNat = n ∧
          (loadWord St.memory C1).toNat = (addDigitLists (xs.take i) (ys.take i) 0).2 ∧
          (addDigitLists (xs.take i) (ys.take i) 0).2 ≤ 1 ∧
          yLimbs St.memory dst n = (addDigitLists (xs.take i) (ys.take i) 0).1 ++ xs.drop i ∧
          (∀ j, i ≤ j → j < n →
            (loadWord St.memory (src + 32 * j)).toNat = lget ys j) ∧
          AddModKeeps St.memory M₀ dst n ∧
          yLimbs St.memory SUBC n = subc₀ ∧
          loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
          loadWord St.memory ASRC = BitVec.ofNat 256 src ∧
          St.activeWords = S.activeWords ∧
            St.env = S.env)
      (P := fun St => yLimbs St.memory dst n = (addDigitLists xs ys 0).1 ∧
        (loadWord St.memory C1).toNat = (addDigitLists xs ys 0).2 ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        yLimbs St.memory SUBC n = subc₀ ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        loadWord St.memory ASRC = BitVec.ofNat 256 src ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env)
      hround hexit (n := n) (yst := S)
      ⟨0, hI2, by omega, hN, by simp [hC1, addDigitLists],
        by simp [addDigitLists], by simp [hxL, addDigitLists],
        fun j _ hj => hyLread j (by omega) hj, hkeeps, hsubcL, hADST, hASRC, rfl,
        rfl⟩
  obtain ⟨hsum, hC1', hN', hkeeps', hsubc', hADST', hASRC', haw', henv'⟩ := hP
  exact ⟨S', hsteps, hsum, hC1', hN', hkeeps', hsubc', hADST', hASRC', haw', henv'⟩

/-- The full subtraction pass: from the loop top to the `lSel` target. -/
theorem subPass_steps [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (suml ms subc₀ : List Nat) (n : Nat)
    (c1 : Nat)
    {cont : List Asm} {σ : List AVal} {S : EvmState} {M₀ : Nat → UInt8}
    (hSub : findLabel l.lSub prog =
      some (amSubBody l ++ amFromSel l ++ cont))
    (hSel : findLabel l.lSel prog =
      some (amSelBody l ++ amFromDoCopy l ++ cont))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hdstN : dst + 32 * n ≤ Ncell)
    (hsubcDst : dst + 32 * n ≤ SUBC)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = 0)
    (hC2 : (loadWord S.memory C2).toNat = 0)
    (hC1 : (loadWord S.memory C1).toNat = c1)
    (hADST : loadWord S.memory ADST = BitVec.ofNat 256 dst)
    (hdstL : yLimbs S.memory dst n = suml)
    (hmodL : yLimbs S.memory MOD n = ms)
    (hsubcL : yLimbs S.memory SUBC n = subc₀)
    (hsumlen : suml.length = n) (hmslen : ms.length = n) (hsubc0len : subc₀.length = n)
    (hsd : ∀ d ∈ suml, d < radix) (hmd : ∀ d ∈ ms, d < radix)
    (hkeeps : AddModKeeps S.memory M₀ dst n) :
    ∃ S', ASteps prog
        ⟨amSubBody l ++ amFromSel l ++ cont, σ, S⟩
        ⟨amSelBody l ++ amFromDoCopy l ++ cont, σ, S'⟩ ∧
      yLimbs S'.memory SUBC n = (subDigitLists suml ms 0).1 ∧
      (loadWord S'.memory C2).toNat = (subDigitLists suml ms 0).2 ∧
      (loadWord S'.memory C1).toNat = c1 ∧
      yLimbs S'.memory dst n = suml ∧
      yLimbs S'.memory MOD n = ms ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      AddModKeeps S'.memory M₀ dst n ∧
      loadWord S'.memory ADST = BitVec.ofNat 256 dst ∧
      S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hround : ∀ {m : Nat} {St : EvmState}, 0 < m →
      (∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        (loadWord St.memory C2).toNat = (subDigitLists (suml.take i) (ms.take i) 0).2 ∧
        (subDigitLists (suml.take i) (ms.take i) 0).2 ≤ 1 ∧
        (loadWord St.memory C1).toNat = c1 ∧
        yLimbs St.memory SUBC n =
          (subDigitLists (suml.take i) (ms.take i) 0).1 ++ subc₀.drop i ∧
        yLimbs St.memory dst n = suml ∧
        yLimbs St.memory MOD n = ms ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) →
      ((∃ St', (∃ i, (loadWord St'.memory I2).toNat = i ∧ i + (m - 1) = n ∧
        (loadWord St'.memory Ncell).toNat = n ∧
        (loadWord St'.memory C2).toNat = (subDigitLists (suml.take i) (ms.take i) 0).2 ∧
        (subDigitLists (suml.take i) (ms.take i) 0).2 ≤ 1 ∧
        (loadWord St'.memory C1).toNat = c1 ∧
        yLimbs St'.memory SUBC n =
          (subDigitLists (suml.take i) (ms.take i) 0).1 ++ subc₀.drop i ∧
        yLimbs St'.memory dst n = suml ∧
        yLimbs St'.memory MOD n = ms ∧
        AddModKeeps St'.memory M₀ dst n ∧
        loadWord St'.memory ADST = BitVec.ofNat 256 dst ∧
        St'.activeWords = S.activeWords ∧
          St'.env = S.env) ∧
        ASteps prog ⟨amSubBody l ++ amFromSel l ++ cont, σ, St⟩
          ⟨amSubBody l ++ amFromSel l ++ cont, σ, St'⟩) ∨
      ((yLimbs St.memory SUBC n = (subDigitLists suml ms 0).1 ∧
        (loadWord St.memory C2).toNat = (subDigitLists suml ms 0).2 ∧
        (loadWord St.memory C1).toNat = c1 ∧
        yLimbs St.memory dst n = suml ∧
        yLimbs St.memory MOD n = ms ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) ∧
        ASteps prog ⟨amSubBody l ++ amFromSel l ++ cont, σ, St⟩
          ⟨amSelBody l ++ amFromDoCopy l ++ cont, σ, St⟩)) := by
    intro m St _hmpos hm
    rcases hm with ⟨i, hI2i, him, hNst, hC2st, hble, hC1st, hsubcst, hdstst, hmodst,
      hkeepsst, hADSTst, hawEq, henvEq⟩
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · exact absurd hm0 (by omega)
    · left
      have hin : i < n := by omega
      have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by rw [hawEq]; exact haw
      have hsd' : lget suml i < radix := by
        have himem : suml[i]'(show i < suml.length by omega) ∈ suml :=
          mem_getElem (show i < suml.length by omega)
        rw [lget_eq (show i < suml.length by omega)]
        exact hsd _ himem
      have hmd' : lget ms i < radix := by
        have himem : ms[i]'(show i < ms.length by omega) ∈ ms :=
          mem_getElem (show i < ms.length by omega)
        rw [lget_eq (show i < ms.length by omega)]
        exact hmd _ himem
      obtain ⟨S', hsteps, hI2', hN', hC2', hble', hC1', hsubc', hdst', hmod',
        hkeeps', hADST', hawEq', henvEq'⟩ :=
        subRound_steps (dst := dst) (src := src) (l := l)
          (suml := suml) (ms := ms) (subc₀ := subc₀) (n := n) (i := i)
          (subDigitLists (suml.take i) (ms.take i) 0).1
          (subDigitLists (suml.take i) (ms.take i) 0).2 c1
          (k := amFromSel l ++ cont) hSub hawSt hin hn32 hdstN hsubcDst hNst
          hI2i hble hC2st hC1st hADSTst rfl hdstst hmodst hsubcst hsumlen hmslen hsubc0len
          hsd' hmd' hkeepsst
      have hawEq'' : S'.activeWords = S.activeWords := by rw [hawEq', hawEq]
      have henvEq'' : S'.env = S.env := by rw [henvEq']; exact henvEq
      exact ⟨S', ⟨i + 1, hI2', by omega, hN', hC2', hble', hC1', hsubc', hdst',
        hmod', hkeeps', hADST', hawEq'', henvEq''⟩, hsteps⟩
  have hexit : ∀ (St : EvmState),
      (∃ i, (loadWord St.memory I2).toNat = i ∧ i + 0 = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        (loadWord St.memory C2).toNat = (subDigitLists (suml.take i) (ms.take i) 0).2 ∧
        (subDigitLists (suml.take i) (ms.take i) 0).2 ≤ 1 ∧
        (loadWord St.memory C1).toNat = c1 ∧
        yLimbs St.memory SUBC n =
          (subDigitLists (suml.take i) (ms.take i) 0).1 ++ subc₀.drop i ∧
        yLimbs St.memory dst n = suml ∧
        yLimbs St.memory MOD n = ms ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) →
      ((yLimbs St.memory SUBC n = (subDigitLists suml ms 0).1 ∧
        (loadWord St.memory C2).toNat = (subDigitLists suml ms 0).2 ∧
        (loadWord St.memory C1).toNat = c1 ∧
        yLimbs St.memory dst n = suml ∧
        yLimbs St.memory MOD n = ms ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env) ∧
        ASteps prog ⟨amSubBody l ++ amFromSel l ++ cont, σ, St⟩
          ⟨amSelBody l ++ amFromDoCopy l ++ cont, σ, St⟩) := by
    intro St hm
    rcases hm with ⟨i, hI2i, him, hNst, hC2st, -, hC1st, hsubcst, hdstst, hmodst,
      hkeepsst, hADSTst, hawEq, henvEq⟩
    have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by rw [hawEq]; exact haw
    have hin : i = n := by omega
    refine ⟨⟨?_, ?_, hC1st, hdstst, hmodst, hNst, hkeepsst, hADSTst, hawEq, henvEq⟩, ?_⟩
    · rw [hsubcst, hin]
      have h1 : suml.take n = suml := take_eq_of_length suml n (by omega)
      have h2 : ms.take n = ms := take_eq_of_length ms n (by omega)
      have h3 : subc₀.drop n = [] := drop_eq_nil_of_length subc₀ n (by omega)
      simp [h1, h2, h3]
    · rw [hC2st, hin]
      have h1 : suml.take n = suml := take_eq_of_length suml n (by omega)
      have h2 : ms.take n = ms := take_eq_of_length ms n (by omega)
      simp [h1, h2]
    · exact exitTest_taken (prog := prog) hawSt hNst hI2i (by omega) (by omega) hSel
  obtain ⟨S', hP, hsteps⟩ :=
    loop_counted (model := model) (prog := prog)
      (top := amSubBody l ++ amFromSel l ++ cont)
      (σ := σ)
      (c' := amSelBody l ++ amFromDoCopy l ++ cont)
      (Inv := fun St m =>
        ∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
          (loadWord St.memory Ncell).toNat = n ∧
          (loadWord St.memory C2).toNat = (subDigitLists (suml.take i) (ms.take i) 0).2 ∧
          (subDigitLists (suml.take i) (ms.take i) 0).2 ≤ 1 ∧
          (loadWord St.memory C1).toNat = c1 ∧
          yLimbs St.memory SUBC n =
            (subDigitLists (suml.take i) (ms.take i) 0).1 ++ subc₀.drop i ∧
          yLimbs St.memory dst n = suml ∧
          yLimbs St.memory MOD n = ms ∧
          AddModKeeps St.memory M₀ dst n ∧
          loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
          St.activeWords = S.activeWords ∧
            St.env = S.env)
      (P := fun St => yLimbs St.memory SUBC n = (subDigitLists suml ms 0).1 ∧
        (loadWord St.memory C2).toNat = (subDigitLists suml ms 0).2 ∧
        (loadWord St.memory C1).toNat = c1 ∧
        yLimbs St.memory dst n = suml ∧
        yLimbs St.memory MOD n = ms ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env)
      hround hexit (n := n) (yst := S)
      ⟨0, hI2, by omega, hN, by simp [hC2, subDigitLists],
        by simp [subDigitLists], hC1, by simp [hsubcL, subDigitLists], hdstL, hmodL,
        hkeeps, hADST, rfl, rfl⟩
  obtain ⟨hsubc, hC2', hC1', hdst', hmod', hN', hkeeps', hADST', haw', henv'⟩ := hP
  exact ⟨S', hsteps, hsubc, hC2', hC1', hdst', hmod', hN', hkeeps', hADST', haw',
    henv'⟩

/-! ## The copy loop -/

/-- One round of the copy loop: `dst[i] := SUBC[i]` (the `dst` address
through the `ADST` cell), `I2++`. -/
theorem copyRound_steps [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (cand suml : List Nat) (n i : Nat)
    {M₀ : Nat → UInt8}
    {k : List Asm} {σ : List AVal} {S : EvmState}
    (hCopy : findLabel l.lCopy prog = some (amCopyBody l ++ k))
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hi : i < n) (hn32 : n ≤ 32)
    (hdstN : dst + 32 * n ≤ Ncell)
    (hsubcDst : dst + 32 * n ≤ SUBC)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = i)
    (hADST : loadWord S.memory ADST = BitVec.ofNat 256 dst)
    (hdstL : yLimbs S.memory dst n = cand.take i ++ suml.drop i)
    (hsubcL : yLimbs S.memory SUBC n = cand)
    (hcandlen : cand.length = n) (hsumlen : suml.length = n)
    (hcd : lget cand i < radix)
    (hkeeps : AddModKeeps S.memory M₀ dst n) :
    ∃ S', ASteps prog ⟨amCopyBody l ++ k, σ, S⟩
        ⟨amCopyBody l ++ k, σ, S'⟩ ∧
      (loadWord S'.memory I2).toNat = i + 1 ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      yLimbs S'.memory dst n = cand.take (i + 1) ++ suml.drop (i + 1) ∧
      yLimbs S'.memory SUBC n = cand ∧
      AddModKeeps S'.memory M₀ dst n ∧
      loadWord S'.memory ADST = BitVec.ofNat 256 dst ∧
      S'.activeWords = S.activeWords ∧
      S'.env = S.env := by
  have hsubcEq : SUBC = 0x1400 := rfl
  have hncell : Ncell = 0x1cc0 := rfl
  have hnclt : (0x1cc0 : Nat) < 2 ^ 256 := by decide
  have hI2c : I2 = 0x1e60 := rfl
  have hi256 : i < 2 ^ 256 := by omega
  have hI2w : loadWord S.memory I2 = BitVec.ofNat 256 i := word_of_toNat hI2 hi256
  have hmod0 : (MOD : Nat) = 0 := rfl
  have hcandlen' : i < cand.length := by omega
  have hsumlen' : i < suml.length := by omega
  have hcid : lget cand i = cand[i]'hcandlen' := lget_eq hcandlen'
  have hcidlt : (cand[i]'hcandlen') < radix := by rw [← hcid]; exact hcd
  -- the two states
  set S₁ : EvmState := {S with memory :=
    (storeWord S.memory (dst + 32 * i) (BitVec.ofNat 256 (lget cand i)))} with hS₁def
  set S₂ : EvmState := {S₁ with memory :=
    (storeWord S₁.memory I2 (BitVec.ofNat 256 (i + 1)))} with hS₂def
  have hS₁mem : S₁.memory =
      storeWord S.memory (dst + 32 * i) (BitVec.ofNat 256 (lget cand i)) := rfl
  have hS₂mem : S₂.memory =
      storeWord S₁.memory I2 (BitVec.ofNat 256 (i + 1)) := rfl
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := haw
  -- value facts
  have hcandL : (loadWord S.memory (SUBC + 32 * i)).toNat = lget cand i :=
    yLimb_lget hi hsubcL (by omega)
  have hcandw : loadWord S.memory (SUBC + 32 * i) =
      BitVec.ofNat 256 (lget cand i) := word_of_toNat hcandL (by omega)
  have hsubci : SUBC + 32 * i < 2 ^ 256 := by omega
  have hdsti : dst + 32 * i < 2 ^ 256 := by omega
  have hI2₁ : loadWord S₁.memory I2 = BitVec.ofNat 256 i := by
    rw [hS₁mem, loadWord_storeWord_disj (p := dst + 32 * i) (q := I2) (by omega)]
    exact hI2w
  have haddr : evalExpr (.bin .add (.load ADST) (.bin .mul (.imm 32) (.load I2))) S
      = BitVec.ofNat 256 (dst + 32 * i) := by
    simp only [evalExpr, evalBin, hADST, hI2w, ofNat_mul256, ofNat_add256]
  have haddr2 : evalExpr
        (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2))) S
      = BitVec.ofNat 256 (SUBC + 32 * i) := by
    simp only [evalExpr, evalBin, hI2w, ofNat_mul256, ofNat_add256]
  have hval : evalExpr
        (loadAt (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2)))) S
      = BitVec.ofNat 256 (lget cand i) := by
    show loadWord S.memory
        (evalExpr (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2))) S).toNat = _
    rw [show evalExpr (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2))) S =
        BitVec.ofNat 256 (SUBC + 32 * i) from by
      simp only [evalExpr, evalBin, hI2w, ofNat_mul256, ofNat_add256],
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsubci]
    exact hcandw
  have htk : cand.take (i + 1) = cand.take i ++ [cand[i]'hcandlen'] := by
    simp [List.take_add_one]
  -- the chain
  have hsteps : ASteps prog ⟨amCopyBody l ++ k, σ, S⟩
      ⟨amCopyBody l ++ k, σ, S₂⟩ := by
    rw [amCopyBody_eq l k]
    refine (exitTest_fall (prog := prog) haw hN hI2 (by omega) hi).trans ?_
    refine (storeAt_val (prog := prog)
      (addrE := .bin .add (.load ADST) (.bin .mul (.imm 32) (.load I2)))
      (valE := loadAt (.bin .add (.imm SUBC) (.bin .mul (.imm 32) (.load I2))))
      (addr := dst + 32 * i) (w := BitVec.ofNat 256 (lget cand i))
      haddr hval hdsti
      ⟨by
        rw [haddr2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsubci]
        show SUBC + 32 * i + 32 ≤ 32 * S.activeWords.toNat
        omega,
        ⟨rfl, True.intro, ⟨rfl, True.intro,
          exprOK_load_cell haw (by simp [fragCells])⟩⟩⟩
      ⟨rfl, exprOK_load_cell haw (by simp [fragCells]),
        ⟨rfl, True.intro, exprOK_load_cell haw (by simp [fragCells])⟩⟩
      (by
        show dst + 32 * i + 32 ≤ 32 * S.activeWords.toNat
        omega)).trans ?_
    refine (incr_I2_steps (prog := prog) (yst := S₁) haw hI2₁ hi256).trans ?_
    exact ASteps.single (astep_jump hCopy)
  refine ⟨S₂, hsteps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hS₂mem, loadWord_storeWord, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i + 1 < 2 ^ 256)]
  · have hNc : loadWord S₂.memory Ncell = loadWord S.memory Ncell := by
      rw [hS₂mem, hS₁mem]
      rw [loadWord_storeWord_disj (p := I2) (q := Ncell)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
        loadWord_storeWord_disj (p := dst + 32 * i) (q := Ncell)
        (by have := fragCells_ge Ncell (by simp [fragCells]); omega)]
    rw [hNc]; exact hN
  · rw [hS₂mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₁mem,
      yLimbs_storeWord S.memory dst n i hi (BitVec.ofNat 256 (lget cand i)),
      show (BitVec.ofNat 256 (lget cand i)).toNat = cand[i]'hcandlen' from by
        rw [hcid, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : cand[i]'hcandlen' < 2 ^ 256)],
      hdstL, drop_cons_of_lt suml i hsumlen',
      set_append_mid' (show (cand.take i).length = i from by
        simp only [List.length_take, hcandlen]; omega)]
    rw [htk, List.append_assoc]
    rfl
  · rw [hS₂mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)), hS₁mem,
      yLimbs_storeWord_disjoint (q := dst + 32 * i)
        (Or.inl (by omega))]
    exact hsubcL
  · rw [hS₂mem, hS₁mem]
    exact keeps_storeWord_cell (keeps_storeWord_dst hkeeps
      ⟨by omega, by omega⟩) (by decide)
  · -- ADST preserved
    rw [hS₂mem, hS₁mem]
    rw [loadWord_storeWord_disj (p := I2) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := dst + 32 * i) (q := ADST)
      (by have := fragCells_ge ADST (by simp [fragCells]); omega)]
    exact hADST
  · rfl
  · rfl

set_option maxHeartbeats 64000000 in
-- The full copy loop: from the loop top to the `lDone` target.
theorem copyLoop_steps [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (cand suml : List Nat) (n : Nat)
    {cont : List Asm} {σ : List AVal} {S : EvmState} {M₀ : Nat → UInt8}
    (hCopy : findLabel l.lCopy prog =
      some (amCopyBody l ++ amFromDone l ++ cont))
    (hDone : findLabel l.lDone prog = some cont)
    (haw : 0x1f40 ≤ 32 * S.activeWords.toNat)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hdstN : dst + 32 * n ≤ Ncell)
    (hsubcDst : dst + 32 * n ≤ SUBC)
    (hN : (loadWord S.memory Ncell).toNat = n)
    (hI2 : (loadWord S.memory I2).toNat = 0)
    (hADST : loadWord S.memory ADST = BitVec.ofNat 256 dst)
    (hdstL : yLimbs S.memory dst n = suml)
    (hsubcL : yLimbs S.memory SUBC n = cand)
    (hcandlen : cand.length = n) (hsumlen : suml.length = n)
    (hcd : ∀ d ∈ cand, d < radix)
    (hkeeps : AddModKeeps S.memory M₀ dst n) :
    ∃ S', ASteps prog
        ⟨amCopyBody l ++ amFromDone l ++ cont, σ, S⟩
        ⟨cont, σ, S'⟩ ∧
      yLimbs S'.memory dst n = cand ∧
      (loadWord S'.memory Ncell).toNat = n ∧
      AddModKeeps S'.memory M₀ dst n ∧
      loadWord S'.memory ADST = BitVec.ofNat 256 dst ∧
      S'.activeWords = S.activeWords ∧ S'.env = S.env := by
  have hyL : ∀ (i : Nat), i < n → lget cand i < radix := by
    intro i hi
    have himem : cand[i]'(show i < cand.length by omega) ∈ cand :=
      mem_getElem (show i < cand.length by omega)
    rw [lget_eq (show i < cand.length by omega)]
    exact hcd _ himem
  obtain ⟨S', hP, hsteps⟩ :=
    loop_counted (model := model) (prog := prog)
      (top := amCopyBody l ++ amFromDone l ++ cont)
      (σ := σ)
      (c' := cont)
      (Inv := fun St m => ∃ i, (loadWord St.memory I2).toNat = i ∧ i + m = n ∧
        (loadWord St.memory Ncell).toNat = n ∧
        yLimbs St.memory dst n = cand.take i ++ suml.drop i ∧
        yLimbs St.memory SUBC n = cand ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧
          St.env = S.env)
      (P := fun St => yLimbs St.memory dst n = cand ∧
        (loadWord St.memory Ncell).toNat = n ∧
        AddModKeeps St.memory M₀ dst n ∧
        loadWord St.memory ADST = BitVec.ofNat 256 dst ∧
        St.activeWords = S.activeWords ∧ St.env = S.env)
      (fun {m St} _hmpos hm => by
        rcases hm with ⟨i, hI2i, him, hNst, hdstst, hsubcst, hkeepsst, hADSTst, hawEq,
          henvEq⟩
        rcases Nat.eq_zero_or_pos m with hm0 | hmpos
        · exact absurd hm0 (by omega)
        · left
          have hin : i < n := by omega
          have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
            rw [hawEq]; exact haw
          obtain ⟨S', hsteps, hI2', hN', hdst', hsubc', hkeeps', hADST', hawEq',
            henvEq'⟩ :=
            copyRound_steps (dst := dst) (src := src) (l := l) (cand := cand)
              (suml := suml)
              (n := n) (i := i)
              (k := amFromDone l ++ cont) hCopy hawSt hin hn32 hdstN hsubcDst
              hNst hI2i hADSTst hdstst hsubcst hcandlen hsumlen (hyL i hin) hkeepsst
          have hawEq'' : S'.activeWords = S.activeWords := by rw [hawEq', hawEq]
          have henvEq'' : S'.env = S.env := by rw [henvEq']; exact henvEq
          exact ⟨S', ⟨i + 1, hI2', by omega, hN', hdst',
            hsubc', hkeeps', hADST', hawEq'', henvEq''⟩, hsteps⟩)
      (fun St hm => by
        rcases hm with ⟨i, hI2i, him, hNst, hdstst, -, hkeepsst, hADSTst, hawEq, henvEq⟩
        have hawSt : 0x1f40 ≤ 32 * St.activeWords.toNat := by
          rw [hawEq]; exact haw
        have hin : i = n := by omega
        refine ⟨⟨?_, hNst, hkeepsst, hADSTst, hawEq, henvEq⟩, ?_⟩
        · rw [hdstst, hin]
          have h1 : cand.take n = cand := take_eq_of_length cand n (by omega)
          have h2 : suml.drop n = [] := drop_eq_nil_of_length suml n (by omega)
          simp [h1, h2]
        · exact exitTest_taken (prog := prog) hawSt hNst hI2i (by omega) (by omega) hDone)
      (n := n) (yst := S)
      ⟨0, hI2, by omega, hN, by simp [hdstL, List.drop_zero], hsubcL, hkeeps, hADST,
        rfl, rfl⟩
  obtain ⟨hdst', hN', hkeeps', hADST', haw', henv'⟩ := hP
  exact ⟨S', hsteps, hdst', hN', hkeeps', hADST', haw', henv'⟩

/-! ## The body theorem -/

/-- The `addMod` procedure body: from a state whose `dst` region represents
`x`, `src` region represents `y`, and `MOD` region represents `m` (all
`n`-limb, `0 < n ≤ 32`, `0 < m`, `x < m`, `y ≤ m`), whose `ADST`/`ASRC`
cells hold `dst`/`src`, and with any stack `σ` (at a call site this is
`.code lret :: caller-frame`), the body — from `store C1 (.imm 0)` through
`.label l.lDone` — runs in place against any continuation `cont` and
reaches `cont` with the stack unchanged, the `dst` region representing
`(x + y) % m`, `Ncell` still holding `n`, and every byte outside the `dst`
and `SUBC` regions and the eight scratch cells (`C1, C2, I2, AOFF, AX, AY,
AS, AZ`) unchanged — a set that includes the `ADST`/`ASRC` cells
themselves, which the body preserves.

Callers instantiate `prog := programAsm` with the concrete label bundle,
discharge the seven `findLabel` facts by `decide`, and compose with
`ASteps.trans`.  `cont` at a call site is `[.dynJump] ++ tail`. -/
theorem amProcFrag_correct [model : ExternalModel] {prog : List Asm}
    (dst src : Nat) (l : AddModProcLabels) (n m x y : Nat)
    (cont : List Asm) (σ : List AVal) (yst : EvmState)
    (hAdd : findLabel l.lAdd prog =
      some (amAddBody l ++ amFromSubStart l ++ cont))
    (hSubStart : findLabel l.lSubStart prog =
      some (store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont))
    (hSub : findLabel l.lSub prog =
      some (amSubBody l ++ amFromSel l ++ cont))
    (hSel : findLabel l.lSel prog =
      some (amSelBody l ++ amFromDoCopy l ++ cont))
    (hDoCopy : findLabel l.lDoCopy prog =
      some (store I2 (.imm 0) ++ amFromCopy l ++ cont))
    (hCopy : findLabel l.lCopy prog =
      some (amCopyBody l ++ amFromDone l ++ cont))
    (hDone : findLabel l.lDone prog = some cont)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hN : (loadWord yst.memory Ncell).toNat = n)
    (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hdstN : dst + 32 * n ≤ Ncell) (hsrcN : src + 32 * n ≤ Ncell)
    (hmodDst : MOD + 32 * n ≤ dst) (hmodSrc : MOD + 32 * n ≤ src)
    (hds : src + 32 * n ≤ dst ∨ dst + 32 * n ≤ src ∨ src = dst)
    (hsubcDst : dst + 32 * n ≤ SUBC) (hsubcSrc : src + 32 * n ≤ SUBC)
    (hADST : loadWord yst.memory ADST = BitVec.ofNat 256 dst)
    (hASRC : loadWord yst.memory ASRC = BitVec.ofNat 256 src)
    (hm : RepresentsY yst.memory MOD n m) (hm0 : 0 < m)
    (hx : RepresentsY yst.memory dst n x) (hxm : x < m)
    (hy : RepresentsY yst.memory src n y) (hym : y ≤ m) :
    ∃ yst', ASteps prog ⟨amProcFrag l ++ cont, σ, yst⟩ ⟨cont, σ, yst'⟩ ∧
      RepresentsY yst'.memory dst n ((x + y) % m) ∧
      (loadWord yst'.memory Ncell).toNat = n ∧
      (∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
        (∀ c ∈ addModScratch, a < c ∨ c + 32 ≤ a) → yst'.memory a = yst.memory a) ∧
      yst'.activeWords = yst.activeWords ∧ yst'.env = yst.env := by
  have hmod0 : (MOD : Nat) = 0 := rfl
  have hncellEq : Ncell = 0x1cc0 := rfl
  have hnclt : (0x1cc0 : Nat) < 2 ^ 256 := by decide
  have hI2Eq : I2 = 0x1e60 := rfl
  have hC1Eq : C1 = 0x1d40 := rfl
  have hC2Eq : C2 = 0x1d60 := rfl
  have hADSTEq : ADST = 0x1e20 := rfl
  have hASRCEq : ASRC = 0x1e40 := rfl
  have hsubcEq : SUBC = 0x1400 := rfl
  have hmodSubc : MOD + 32 * n ≤ SUBC := by omega
  -- lists
  have hxlen : (yLimbs yst.memory dst n).length = n := length_yLimbs yst.memory dst n
  have hylen : (yLimbs yst.memory src n).length = n := length_yLimbs yst.memory src n
  have hmslen : (yLimbs yst.memory MOD n).length = n := length_yLimbs yst.memory MOD n
  have hxd : ∀ d ∈ yLimbs yst.memory dst n, d < radix := fun d hd => yLimb_lt hd
  have hyd : ∀ d ∈ yLimbs yst.memory src n, d < radix := fun d hd => yLimb_lt hd
  have hmd : ∀ d ∈ yLimbs yst.memory MOD n, d < radix := fun d hd => yLimb_lt hd
  have hxv : Nat.ofDigits radix (yLimbs yst.memory dst n) = x := value_of_RepresentsY hx
  have hyv : Nat.ofDigits radix (yLimbs yst.memory src n) = y := value_of_RepresentsY hy
  have hmv : Nat.ofDigits radix (yLimbs yst.memory MOD n) = m := value_of_RepresentsY hm
  -- phase 0: init stores + label
  set S₁' : EvmState := {yst with memory :=
      (storeWord yst.memory C1 (BitVec.ofNat 256 0))} with hS₁'def
  have s0 : ASteps prog ⟨amProcFrag l ++ cont, σ, yst⟩
      ⟨amAddBody l ++ amFromSubStart l ++ cont,
        σ, {S₁' with memory :=
          (storeWord S₁'.memory I2 (BitVec.ofNat 256 0))}⟩ := by
    have hs := store_cell_val (prog := prog) (c := C1) (e := .imm 0)
      (w := BitVec.ofNat 256 0)
      (k := store I2 (.imm 0) ++ [.label l.lAdd] ++ amAddBody l ++
        amFromSubStart l ++ cont)
      (σ := σ) rfl True.intro
      (cell_pinned haw (by simp [fragCells]))
    have h0 := store_cell_val (prog := prog) (c := I2) (e := .imm 0)
      (w := BitVec.ofNat 256 0)
      (k := [.label l.lAdd] ++ amAddBody l ++
        amFromSubStart l ++ cont)
      (σ := σ) (yst := S₁') rfl True.intro
      (cell_pinned haw (by simp [fragCells]))
    rw [amProcFrag_split l]
    exact (hs.trans h0).trans (label_steps (prog := prog) (l := l.lAdd) (σ := σ)
      (yst := {S₁' with memory := (storeWord S₁'.memory I2 (BitVec.ofNat 256 0))})
      (k := amAddBody l ++ amFromSubStart l ++ cont))
  set S₀ : EvmState := {yst with memory :=
      (storeWord (storeWord yst.memory C1 (BitVec.ofNat 256 0)) I2
        (BitVec.ofNat 256 0))} with hS₀def
  have hS₀mem : S₀.memory =
      storeWord (storeWord yst.memory C1 (BitVec.ofNat 256 0)) I2
        (BitVec.ofNat 256 0) := rfl
  have hawS₀ : 0x1f40 ≤ 32 * S₀.activeWords.toNat := haw
  -- init-state facts
  have hI2₀ : (loadWord S₀.memory I2).toNat = 0 := by
    rw [hS₀mem, loadWord_storeWord, BitVec.toNat_ofNat]
  have hC1₀ : (loadWord S₀.memory C1).toNat = 0 := by
    rw [hS₀mem, loadWord_storeWord_disj (p := I2) (q := C1)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord, BitVec.toNat_ofNat]
  have hN₀ : (loadWord S₀.memory Ncell).toNat = n := by
    rw [hS₀mem, loadWord_storeWord_disj (p := I2) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := C1) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN
  have hADST₀ : loadWord S₀.memory ADST = BitVec.ofNat 256 dst := by
    rw [hS₀mem, loadWord_storeWord_disj (p := I2) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := C1) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hADST
  have hASRC₀ : loadWord S₀.memory ASRC = BitVec.ofNat 256 src := by
    rw [hS₀mem, loadWord_storeWord_disj (p := I2) (q := ASRC)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := C1) (q := ASRC)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hASRC
  have hdstL₀ : yLimbs S₀.memory dst n = yLimbs yst.memory dst n := by
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := C1)
      (Or.inr (by have := fragCells_ge C1 (by simp [fragCells]); omega))]
  have hsrcL₀ : yLimbs S₀.memory src n = yLimbs yst.memory src n := by
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := C1)
      (Or.inr (by have := fragCells_ge C1 (by simp [fragCells]); omega))]
  have hkeeps₀ : AddModKeeps S₀.memory yst.memory dst n := by
    rw [hS₀mem]
    exact keeps_storeWord_cell (keeps_storeWord_cell (keeps_refl _ _ _)
      (by decide)) (by decide)
  have hmodL₀ : yLimbs S₀.memory MOD n = yLimbs yst.memory MOD n :=
    yLimbs_of_keeps hkeeps₀ (Or.inl (by omega)) (by omega)
      (fun c hc => by have := fragCells_ge c (scratch_cells hc); omega)
  have hsubcL₀ : yLimbs S₀.memory SUBC n = yLimbs yst.memory SUBC n := by
    rw [hS₀mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := C1)
      (Or.inr (by have := fragCells_ge C1 (by simp [fragCells]); omega))]
  -- phase 1: the addition pass
  obtain ⟨S₁, hp1, hsumL, hC1₁, hN₁, hkeeps₁, hsubcL₁, hADST₁, hASRC₁, hawEq₁,
    henvEq₁⟩ :=
    addPass_steps (dst := dst) (src := src) (l := l)
      (xs := yLimbs yst.memory dst n) (ys := yLimbs yst.memory src n)
      (subc₀ := yLimbs yst.memory SUBC n) (n := n)
      (cont := cont) (σ := σ) (S := S₀) (M₀ := yst.memory)
      hAdd hSubStart hawS₀ hn hn32 hdstN hsrcN hsubcDst hds hN₀ hI2₀ hC1₀ hADST₀
      hASRC₀ hdstL₀ hsrcL₀
      hxlen hylen hxd hyd hsubcL₀ hkeeps₀
  -- phase 2: init stores + subtraction pass
  have s2a : ASteps prog
      ⟨store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ cont, σ, S₁⟩
      ⟨amSubBody l ++ amFromSel l ++ cont, σ,
        {S₁ with memory :=
          (storeWord (storeWord S₁.memory C2 (BitVec.ofNat 256 0)) I2
            (BitVec.ofNat 256 0))}⟩ := by
    set S₂a : EvmState := {S₁ with memory :=
      (storeWord S₁.memory C2 (BitVec.ofNat 256 0))} with hS₂adef
    have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := by
      rw [hawEq₁]; exact hawS₀
    have hawS₂a : 0x1f40 ≤ 32 * S₂a.activeWords.toNat := hawS₁
    have hs := store_cell_val (prog := prog) (c := C2) (e := .imm 0)
      (w := BitVec.ofNat 256 0)
      (k := store I2 (.imm 0) ++ [.label l.lSub] ++ amSubBody l ++
        amFromSel l ++ cont)
      (σ := σ) (yst := S₁) rfl True.intro
      (cell_pinned hawS₁ (by simp [fragCells]))
    set S₂b : EvmState := {S₂a with memory :=
      (storeWord S₂a.memory I2 (BitVec.ofNat 256 0))} with hS₂bdef
    have h0 := store_cell_val (prog := prog) (c := I2) (e := .imm 0)
      (w := BitVec.ofNat 256 0)
      (k := [.label l.lSub] ++ amSubBody l ++ amFromSel l ++ cont)
      (σ := σ)
      (yst := S₂a)
      rfl True.intro
      (cell_pinned hawS₂a (by simp [fragCells]))
    exact (hs.trans h0).trans (label_steps (prog := prog) (l := l.lSub) (σ := σ)
      (yst := S₂b)
      (k := amSubBody l ++ amFromSel l ++ cont))
  set S₂₀ : EvmState := {S₁ with memory :=
      (storeWord (storeWord S₁.memory C2 (BitVec.ofNat 256 0)) I2
        (BitVec.ofNat 256 0))} with hS₂₀def
  have hS₂₀mem : S₂₀.memory =
      storeWord (storeWord S₁.memory C2 (BitVec.ofNat 256 0)) I2
        (BitVec.ofNat 256 0) := rfl
  have hawS₂₀ : 0x1f40 ≤ 32 * S₂₀.activeWords.toNat := by
    have haw : S₂₀.activeWords = S₁.activeWords := rfl
    rw [haw, hawEq₁]; exact hawS₀
  have hI2₂₀ : (loadWord S₂₀.memory I2).toNat = 0 := by
    rw [hS₂₀mem, loadWord_storeWord, BitVec.toNat_ofNat]
  have hC2₂₀ : (loadWord S₂₀.memory C2).toNat = 0 := by
    rw [hS₂₀mem, loadWord_storeWord_disj (p := I2) (q := C2)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord, BitVec.toNat_ofNat]
  have hC1₂₀ : (loadWord S₂₀.memory C1).toNat = (addDigitLists
      (yLimbs yst.memory dst n) (yLimbs yst.memory src n) 0).2 := by
    rw [hS₂₀mem, loadWord_storeWord_disj (p := I2) (q := C1)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := C2) (q := C1)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hC1₁
  have hN₂₀ : (loadWord S₂₀.memory Ncell).toNat = n := by
    rw [hS₂₀mem, loadWord_storeWord_disj (p := I2) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := C2) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN₁
  have hADST₂₀ : loadWord S₂₀.memory ADST = BitVec.ofNat 256 dst := by
    rw [hS₂₀mem, loadWord_storeWord_disj (p := I2) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := C2) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hADST₁
  have hdstL₂₀ : yLimbs S₂₀.memory dst n = (addDigitLists
      (yLimbs yst.memory dst n) (yLimbs yst.memory src n) 0).1 := by
    rw [hS₂₀mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := C2)
      (Or.inr (by have := fragCells_ge C2 (by simp [fragCells]); omega))]
    exact hsumL
  have hmodL₁ : yLimbs S₁.memory MOD n = yLimbs yst.memory MOD n :=
    yLimbs_of_keeps hkeeps₁ (Or.inl (by omega)) (by omega)
      (fun c hc => by have := fragCells_ge c (scratch_cells hc); omega)
  have hmodL₂₀ : yLimbs S₂₀.memory MOD n = yLimbs yst.memory MOD n := by
    rw [hS₂₀mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := C2)
      (Or.inr (by have := fragCells_ge C2 (by simp [fragCells]); omega))]
    exact hmodL₁
  have hsubcL₂₀ : yLimbs S₂₀.memory SUBC n = yLimbs yst.memory SUBC n := by
    rw [hS₂₀mem, yLimbs_storeWord_disjoint (q := I2)
      (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega)),
      yLimbs_storeWord_disjoint (q := C2)
      (Or.inr (by have := fragCells_ge C2 (by simp [fragCells]); omega))]
    exact hsubcL₁
  have hkeeps₂₀ : AddModKeeps S₂₀.memory yst.memory dst n := by
    rw [hS₂₀mem]
    exact keeps_storeWord_cell (keeps_storeWord_cell hkeeps₁ (by decide)) (by decide)
  obtain ⟨S₂, hp2, hcandL, hC2₂, hC1₂, hdstL₂, hmodL₂, hN₂, hkeeps₂, hADST₂, hawEq₂,
    henvEq₂⟩ :=
    subPass_steps (dst := dst) (src := src) (l := l)
      (suml := (addDigitLists (yLimbs yst.memory dst n)
        (yLimbs yst.memory src n) 0).1)
      (ms := yLimbs yst.memory MOD n)
      (subc₀ := yLimbs yst.memory SUBC n) (n := n)
      (c1 := (addDigitLists (yLimbs yst.memory dst n)
        (yLimbs yst.memory src n) 0).2)
      (cont := cont) (σ := σ) (S := S₂₀) (M₀ := yst.memory)
      hSub hSel hawS₂₀ hn hn32 hdstN hsubcDst hN₂₀ hI2₂₀ hC2₂₀ hC1₂₀ hADST₂₀ hdstL₂₀
      hmodL₂₀ hsubcL₂₀
      (by rw [length_addDigitLists_left (by simp [hxlen, hylen])]; omega)
      hmslen (length_yLimbs yst.memory SUBC n)
      (fun d hd => addDigitLists_digits_lt hd) hmd hkeeps₂₀
  -- the selection
  set carry := (addDigitLists (yLimbs yst.memory dst n) (yLimbs yst.memory src n) 0).2 with hcarrydef
  set borrow := (subDigitLists (addDigitLists (yLimbs yst.memory dst n)
      (yLimbs yst.memory src n) 0).1 (yLimbs yst.memory MOD n) 0).2 with hborrowdef
  have hcarryle : carry ≤ 1 :=
    addModCarry_le_one (by simp [hxlen, hylen]) hxd hyd
  have hborrowle : borrow ≤ 1 :=
    addModBorrow_le_one (by rw [hxlen, hylen]) (by rw [hylen, hmslen])
  have hC1w₂ : loadWord S₂.memory C1 = BitVec.ofNat 256 carry :=
    word_of_toNat hC1₂ (by omega)
  have hC2w₂ : loadWord S₂.memory C2 = BitVec.ofNat 256 borrow :=
    word_of_toNat hC2₂ (by omega)
  have hcond : evalExpr (.bin .or (.load C1) (.un .iszero (.load C2))) S₂
      = BitVec.ofNat 256 (carry ||| (if borrow = 0 then 1 else 0)) := by
    have hmcarry : carry % 2 ^ 256 = carry := Nat.mod_eq_of_lt (by omega)
    have hmborrow : borrow % 2 ^ 256 = borrow := Nat.mod_eq_of_lt (by omega)
    have key : ∀ hc : carry = 0 ∨ carry = 1, ∀ hb : borrow = 0 ∨ borrow = 1,
        (evalExpr (.bin .or (.load C1) (.un .iszero (.load C2))) S₂).toNat
          = carry ||| (if borrow = 0 then 1 else 0) ∧
        carry ||| (if borrow = 0 then 1 else 0) < 2 ^ 256 := by
      intro hc hb
      rcases hc with hc | hc <;> rcases hb with hb | hb <;>
        simp only [hc, hb, toNat_or_eq, toNat_b2w_eq, evalExpr, evalBin, evalUn,
          hC1w₂, hC2w₂, BitVec.toNat_ofNat] <;>
        first
        | rfl
        | omega
        | decide
    exact word_of_toNat (key (by omega) (by omega)).1 (key (by omega) (by omega)).2
  -- shared value-level facts
  have hvalue : (x + y) % m < radix ^ n :=
    Nat.lt_of_lt_of_le (Nat.mod_lt (x + y) hm0) (Nat.le_of_lt hm.1)
  have hresval : Nat.ofDigits radix
      (addModResult (yLimbs yst.memory dst n) (yLimbs yst.memory src n)
        (yLimbs yst.memory MOD n)) =
      (x + y) % m := by
    have h1 := addModResult_value_le (xs := yLimbs yst.memory dst n)
      (ys := yLimbs yst.memory src n) (ms := yLimbs yst.memory MOD n)
      (by simp [hxlen, hmslen]) (by simp [hylen, hmslen]) hxd hyd hmd
      (by rw [hxv, hmv]; exact hxm) (by rw [hyv, hmv]; exact hym)
    rwa [hxv, hyv, hmv] at h1
  -- the final assembly
  have hawS₂ : 0x1f40 ≤ 32 * S₂.activeWords.toNat := by
    have haw : S₂.activeWords = S₂₀.activeWords := hawEq₂
    rw [haw]; exact hawS₂₀
  rcases (by omega : (carry = 0 ∧ borrow = 1) ∨ (carry = 1 ∨ borrow = 0)) with
    ⟨hc0, hb1⟩ | hcp
  · -- fall-through branch: dst keeps the wrapped sum
    have hz : (BitVec.ofNat 256 (carry ||| (if borrow = 0 then 1 else 0))) = 0 := by
      apply BitVec.eq_of_toNat_eq
      simp [hc0, hb1]
    have hchain : ASteps prog
        ⟨amSelBody l ++ amFromDoCopy l ++ cont, σ, S₂⟩
        ⟨cont, σ, S₂⟩ := by
      rw [show amSelBody l ++ amFromDoCopy l ++ cont
          = jumpIfNz (.bin .or (.load C1) (.un .iszero (.load C2))) l.lDoCopy ++
            ([.jump l.lDone] ++ amFromDoCopy l ++ cont) from by
          simp [amSelBody, List.append_assoc]]
      exact (jumpIfNz_fall (e := .bin .or (.load C1) (.un .iszero (.load C2)))
        (l := l.lDoCopy)
        (k := [.jump l.lDone] ++ amFromDoCopy l ++ cont)
        (σ := σ) (yst := S₂)
        (by
          have hC1v : C1 = 0x1d40 := rfl
          have hC2v : C2 = 0x1d60 := rfl
          exact ⟨rfl, ⟨by decide, by omega⟩, ⟨rfl, ⟨by decide, by omega⟩⟩⟩)
        (by rw [hcond]; exact hz)).trans (jump_steps hDone)
    have hawFin : S₂.activeWords = yst.activeWords :=
      ((hawEq₂.trans rfl).trans hawEq₁).trans rfl
    have henvFin : S₂.env = yst.env :=
      ((henvEq₂.trans rfl).trans henvEq₁).trans rfl
    refine ⟨S₂, (((s0.trans hp1).trans s2a).trans hp2).trans hchain, ?_, hN₂,
      hkeeps₂, hawFin, henvFin⟩
    refine (RepresentsY_iff_value hvalue).mpr ?_
    have hrr : addModResult (yLimbs yst.memory dst n) (yLimbs yst.memory src n)
        (yLimbs yst.memory MOD n) =
        (addDigitLists (yLimbs yst.memory dst n)
          (yLimbs yst.memory src n) 0).1 := by
      simp only [addModResult, addModCarry, addModBorrow, addModCandidate]
      rw [if_neg (by
        intro hcon
        rcases hcon with h | h
        · rw [← hcarrydef] at h; omega
        · rw [← hborrowdef] at h; omega)]
    rw [hrr] at hresval
    rw [hdstL₂]
    exact hresval
  · -- copy branch: dst gets the subtraction candidate
    have hV1 : carry ||| (if borrow = 0 then 1 else 0) = 1 := by
      rcases (by omega : carry = 0 ∨ carry = 1) with h | h
      · have hb : borrow = 0 := by omega
        simp only [h, hb]
        decide
      · rcases (by omega : borrow = 0 ∨ borrow = 1) with hb | hb
        · simp only [h, hb]; decide
        · simp only [h, hb]; decide
    have hne : (BitVec.ofNat 256 (carry ||| (if borrow = 0 then 1 else 0))) ≠ 0 :=
      ofNat_ne_zero (by omega) (by omega)
    set S₃ : EvmState := {S₂ with memory :=
      (storeWord S₂.memory I2 (BitVec.ofNat 256 0))} with hS₃def
    have hS₃mem : S₃.memory = storeWord S₂.memory I2 (BitVec.ofNat 256 0) := rfl
    have hawS₃ : 0x1f40 ≤ 32 * S₃.activeWords.toNat := hawS₂
    have hI2₃ : (loadWord S₃.memory I2).toNat = 0 := by
      rw [hS₃mem, loadWord_storeWord, BitVec.toNat_ofNat]
    have hN₃ : (loadWord S₃.memory Ncell).toNat = n := by
      rw [hS₃mem, loadWord_storeWord_disj (p := I2) (q := Ncell)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
      exact hN₂
    have hADST₃ : loadWord S₃.memory ADST = BitVec.ofNat 256 dst := by
      rw [hS₃mem, loadWord_storeWord_disj (p := I2) (q := ADST)
        (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
      exact hADST₂
    have hdstL₃ : yLimbs S₃.memory dst n = (addDigitLists
        (yLimbs yst.memory dst n) (yLimbs yst.memory src n) 0).1 := by
      rw [hS₃mem, yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega))]
      exact hdstL₂
    have hsubcL₃ : yLimbs S₃.memory SUBC n = (subDigitLists
        (addDigitLists (yLimbs yst.memory dst n)
          (yLimbs yst.memory src n) 0).1 (yLimbs yst.memory MOD n) 0).1 := by
      rw [hS₃mem, yLimbs_storeWord_disjoint (q := I2)
        (Or.inr (by have := fragCells_ge I2 (by simp [fragCells]); omega))]
      exact hcandL
    have hkeeps₃ : AddModKeeps S₃.memory yst.memory dst n := by
      rw [hS₃mem]
      exact keeps_storeWord_cell hkeeps₂ (by decide)
    obtain ⟨S', hcopy, hdstF, hNF, hkeepsF, hADSTF, hawF, henvF⟩ :=
      copyLoop_steps (dst := dst) (src := src) (l := l)
        (cand := (subDigitLists (addDigitLists (yLimbs yst.memory dst n)
            (yLimbs yst.memory src n) 0).1 (yLimbs yst.memory MOD n) 0).1)
        (suml := (addDigitLists (yLimbs yst.memory dst n)
          (yLimbs yst.memory src n) 0).1) (n := n)
        (cont := cont) (σ := σ) (S := S₃) (M₀ := yst.memory)
        hCopy hDone hawS₃ hn hn32 hdstN hsubcDst hN₃ hI2₃ hADST₃ hdstL₃ hsubcL₃
        (by
          rw [length_subDigitLists_left (xs := (addDigitLists (yLimbs yst.memory dst n)
              (yLimbs yst.memory src n) 0).1) (ys := yLimbs yst.memory MOD n)
            (borrow := 0)
            (by simp [length_addDigitLists_left, hxlen, hylen, hmslen]),
            length_addDigitLists_left (by simp [hxlen, hylen])]
          omega)
        (by rw [length_addDigitLists_left (by simp [hxlen, hylen])]; omega)
        (fun d hd => subDigitLists_digits_lt
          (by simp [length_addDigitLists_left, hxlen, hylen, hmslen])
          (fun d' hd' => addDigitLists_digits_lt hd') hmd (by omega) hd)
        hkeeps₃
    have hjump : ASteps prog
        ⟨amSelBody l ++ amFromDoCopy l ++ cont, σ, S₂⟩
        ⟨store I2 (.imm 0) ++ amFromCopy l ++ cont, σ, S₂⟩ := by
      rw [show amSelBody l ++ amFromDoCopy l ++ cont
          = jumpIfNz (.bin .or (.load C1) (.un .iszero (.load C2))) l.lDoCopy ++
            ([.jump l.lDone] ++ [.label l.lDoCopy] ++ store I2 (.imm 0) ++
              amFromCopy l ++ cont) from by
          simp [amSelBody, amFromDoCopy, List.append_assoc]]
      exact jumpIfNz_taken (prog := prog)
        (e := .bin .or (.load C1) (.un .iszero (.load C2)))
        (l := l.lDoCopy) (c' := store I2 (.imm 0) ++ amFromCopy l ++ cont)
        (k := [.jump l.lDone] ++ [.label l.lDoCopy] ++ store I2 (.imm 0) ++
          amFromCopy l ++ cont) (σ := σ) (yst := S₂)
        (by
          have hC1v : C1 = 0x1d40 := rfl
          have hC2v : C2 = 0x1d60 := rfl
          exact ⟨rfl, ⟨by decide, by omega⟩, ⟨rfl, ⟨by decide, by omega⟩⟩⟩)
        (by rw [hcond]; exact hne) hDoCopy
    have hstore := store_cell_val (prog := prog) (c := I2) (e := .imm 0)
      (w := BitVec.ofNat 256 0) (yst := S₂) (σ := σ)
      (k := amFromCopy l ++ cont) rfl True.intro
      (cell_pinned hawS₂ (by simp [fragCells]))
    have hlabel : AStep prog
        ⟨[.label l.lCopy] ++ (amCopyBody l ++ amFromDone l ++ cont), σ, S₃⟩
        ⟨amCopyBody l ++ amFromDone l ++ cont, σ, S₃⟩ :=
      astep_label
    have hawF'' : S'.activeWords = yst.activeWords :=
      ((hawF.trans rfl).trans ((hawEq₂.trans rfl).trans hawEq₁)).trans rfl
    have henvF'' : S'.env = yst.env :=
      ((henvF.trans rfl).trans ((henvEq₂.trans rfl).trans henvEq₁)).trans rfl
    refine ⟨S', (((s0.trans hp1).trans s2a).trans hp2).trans
      (((hjump.trans hstore).trans (ASteps.single hlabel)).trans hcopy), ?_, hNF,
      hkeepsF, hawF'', henvF''⟩
    refine (RepresentsY_iff_value hvalue).mpr ?_
    have hselpos : (addDigitLists (yLimbs yst.memory dst n)
          (yLimbs yst.memory src n) 0).2 = 1 ∨
        (subDigitLists (addDigitLists (yLimbs yst.memory dst n)
          (yLimbs yst.memory src n) 0).1 (yLimbs yst.memory MOD n) 0).2 = 0 := by
      by_cases h1 : carry = 1
      · exact Or.inl (by rw [← hcarrydef]; exact h1)
      · refine Or.inr ?_
        have hb : borrow = 0 := by omega
        rw [← hborrowdef]
        exact hb
    have hrr : addModResult (yLimbs yst.memory dst n) (yLimbs yst.memory src n)
        (yLimbs yst.memory MOD n) =
        (subDigitLists (addDigitLists (yLimbs yst.memory dst n)
          (yLimbs yst.memory src n) 0).1 (yLimbs yst.memory MOD n) 0).1 := by
      simp only [addModResult, addModCarry, addModBorrow, addModCandidate]
      rw [if_pos hselpos]
    rw [hrr] at hresval
    rw [hdstF]
    exact hresval

/-! ## The call-site theorem -/

/-- The complete `addMod` call at a site
`store ADST (.imm dst) ++ store ASRC (.imm src) ++ [.pushLabel lret,
.jump l.lEntry, .label lret] ++ cont`: the two address-register stores run,
the return address is pushed, the procedure body executes with that address
at the bottom of the stack, and the trailing `.dynJump` pops it and lands at
`cont` — with the original stack `σ` throughout, the `dst` region
representing `(x + y) % m`, `Ncell` unchanged, and every byte outside the
`dst`/`SUBC` regions and the ten call-scratch cells (`ADST`, `ASRC`, the
eight body scratch cells — `I2` among them, so the caller's `I2` is
clobbered by the calling convention) unchanged.

`tail` is the program suffix after the procedure's `.dynJump`
(`mulModProc` in `programAsm`); `hfindEntry`/`hfindRet` are the only
call-site-dependent label facts (the seven internal ones are shared by all
call sites).  On `programAsm` every hypothesis is decided by `decide`. -/
theorem addModCall_correct [model : ExternalModel] {prog : List Asm}
    (dst src lret : Nat) (l : AddModProcLabels) (n m x y : Nat)
    (tail : List Asm) (cont : List Asm) (σ : List AVal) (yst : EvmState)
    (hmem : lret ∈ labelDefs prog)
    (hfindEntry : findLabel l.lEntry prog = some (amProcFrag l ++ [.dynJump] ++ tail))
    (hAdd : findLabel l.lAdd prog =
      some (amAddBody l ++ amFromSubStart l ++ [.dynJump] ++ tail))
    (hSubStart : findLabel l.lSubStart prog =
      some (store C2 (.imm 0) ++ store I2 (.imm 0) ++ amFromSub l ++ [.dynJump] ++ tail))
    (hSub : findLabel l.lSub prog =
      some (amSubBody l ++ amFromSel l ++ [.dynJump] ++ tail))
    (hSel : findLabel l.lSel prog =
      some (amSelBody l ++ amFromDoCopy l ++ [.dynJump] ++ tail))
    (hDoCopy : findLabel l.lDoCopy prog =
      some (store I2 (.imm 0) ++ amFromCopy l ++ [.dynJump] ++ tail))
    (hCopy : findLabel l.lCopy prog =
      some (amCopyBody l ++ amFromDone l ++ [.dynJump] ++ tail))
    (hDone : findLabel l.lDone prog = some ([.dynJump] ++ tail))
    (hfindRet : findLabel lret prog = some cont)
    (hn : 0 < n) (hn32 : n ≤ 32)
    (hN : (loadWord yst.memory Ncell).toNat = n)
    (haw : 0x1f40 ≤ 32 * yst.activeWords.toNat)
    (hdstN : dst + 32 * n ≤ Ncell) (hsrcN : src + 32 * n ≤ Ncell)
    (hmodDst : MOD + 32 * n ≤ dst) (hmodSrc : MOD + 32 * n ≤ src)
    (hds : src + 32 * n ≤ dst ∨ dst + 32 * n ≤ src ∨ src = dst)
    (hsubcDst : dst + 32 * n ≤ SUBC) (hsubcSrc : src + 32 * n ≤ SUBC)
    (hm : RepresentsY yst.memory MOD n m) (hm0 : 0 < m)
    (hx : RepresentsY yst.memory dst n x) (hxm : x < m)
    (hy : RepresentsY yst.memory src n y) (hym : y ≤ m) :
    ∃ yst', ASteps prog
      ⟨store ADST (.imm dst) ++ store ASRC (.imm src) ++
        [.pushLabel lret, .jump l.lEntry, .label lret] ++ cont, σ, yst⟩
      ⟨cont, σ, yst'⟩ ∧
      RepresentsY yst'.memory dst n ((x + y) % m) ∧
      (loadWord yst'.memory Ncell).toNat = n ∧
      (∀ a, (a < dst ∨ dst + 32 * n ≤ a) → (a < SUBC ∨ SUBC + 32 * n ≤ a) →
        (∀ c ∈ addModCallScratch, a < c ∨ c + 32 ≤ a) →
        yst'.memory a = yst.memory a) ∧
      yst'.activeWords = yst.activeWords ∧ yst'.env = yst.env := by
  have hncellEq : Ncell = 0x1cc0 := rfl
  have hnclt : (0x1cc0 : Nat) < 2 ^ 256 := by decide
  -- the two address-register stores
  have hpinD : ADST < 2 ^ 256 ∧ ADST + 32 ≤ 32 * yst.activeWords.toNat :=
    cell_pinned haw (by simp [fragCells])
  have hpinS : ASRC < 2 ^ 256 ∧ ASRC + 32 ≤ 32 * yst.activeWords.toNat :=
    cell_pinned haw (by simp [fragCells])
  set Sa : EvmState := {yst with memory :=
    (storeWord yst.memory ADST (BitVec.ofNat 256 dst))} with hSadef
  set S₁ : EvmState := {yst with memory :=
    (storeWord (storeWord yst.memory ADST (BitVec.ofNat 256 dst)) ASRC
      (BitVec.ofNat 256 src))} with hS₁def
  have hSamem : Sa.memory = storeWord yst.memory ADST (BitVec.ofNat 256 dst) := rfl
  have hS₁mem : S₁.memory =
      storeWord (storeWord yst.memory ADST (BitVec.ofNat 256 dst)) ASRC
        (BitVec.ofNat 256 src) := rfl
  have hawSa : 0x1f40 ≤ 32 * Sa.activeWords.toNat := haw
  have hawS₁ : 0x1f40 ≤ 32 * S₁.activeWords.toNat := haw
  have hs1 : ASteps prog ⟨store ADST (.imm dst) ++
      (store ASRC (.imm src) ++ [.pushLabel lret, .jump l.lEntry, .label lret] ++ cont),
      σ, yst⟩
      ⟨store ASRC (.imm src) ++ [.pushLabel lret, .jump l.lEntry, .label lret] ++ cont,
        σ, Sa⟩ :=
    store_cell_val (prog := prog) (c := ADST) (e := .imm dst)
      (w := BitVec.ofNat 256 dst)
      (k := store ASRC (.imm src) ++ [.pushLabel lret, .jump l.lEntry, .label lret]
        ++ cont)
      (σ := σ) rfl True.intro hpinD
  have hs2 : ASteps prog ⟨store ASRC (.imm src) ++
      ([.pushLabel lret, .jump l.lEntry, .label lret] ++ cont), σ, Sa⟩
      ⟨[.pushLabel lret, .jump l.lEntry, .label lret] ++ cont, σ, S₁⟩ :=
    store_cell_val (prog := prog) (c := ASRC) (e := .imm src)
      (w := BitVec.ofNat 256 src)
      (k := [.pushLabel lret, .jump l.lEntry, .label lret] ++ cont)
      (σ := σ) (yst := Sa) rfl True.intro hpinS
  have hs3 : ASteps prog
      ⟨[.pushLabel lret, .jump l.lEntry, .label lret] ++ cont, σ, S₁⟩
      ⟨amProcFrag l ++ [.dynJump] ++ tail, .code lret :: σ, S₁⟩ :=
    call_entry_steps hmem hfindEntry
  -- S₁ satisfies the body theorem's hypotheses
  have hN₁ : (loadWord S₁.memory Ncell).toNat = n := by
    rw [hS₁mem]
    rw [loadWord_storeWord_disj (p := ASRC) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide)),
      loadWord_storeWord_disj (p := ADST) (q := Ncell)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact hN
  have hADST₁ : loadWord S₁.memory ADST = BitVec.ofNat 256 dst := by
    rw [hS₁mem, loadWord_storeWord_disj (p := ASRC) (q := ADST)
      (cells_disj (by simp [fragCells]) (by simp [fragCells]) (by decide))]
    exact loadWord_storeWord _ _ _
  have hASRC₁ : loadWord S₁.memory ASRC = BitVec.ofNat 256 src := by
    rw [hS₁mem]; exact loadWord_storeWord _ _ _
  have hdj : ADST + 32 ≤ ASRC := by decide
  have hcellDst : dst + 32 * n ≤ ADST := by
    have := fragCells_ge ADST (by simp [fragCells]); omega
  have hcellSrcD : src + 32 * n ≤ ADST := by
    have := fragCells_ge ADST (by simp [fragCells]); omega
  have hcellSrc : src + 32 * n ≤ ASRC := by
    have := fragCells_ge ASRC (by simp [fragCells]); omega
  have hmodCellDst : ADST + 32 ≤ dst ∨ dst + 32 * n ≤ ADST := Or.inr hcellDst
  have hx₁ : RepresentsY S₁.memory dst n x :=
    RepresentsY_storeWord_disjoint (RepresentsY_storeWord_disjoint hx
      (q := ADST) hmodCellDst) (q := ASRC) (Or.inr (by omega))
  have hy₁ : RepresentsY S₁.memory src n y :=
    RepresentsY_storeWord_disjoint (RepresentsY_storeWord_disjoint hy
      (q := ADST) (Or.inr (by omega))) (q := ASRC) (Or.inr (by omega))
  have hm₁ : RepresentsY S₁.memory MOD n m :=
    RepresentsY_storeWord_disjoint (RepresentsY_storeWord_disjoint hm
      (q := ADST) (Or.inr (by omega))) (q := ASRC) (Or.inr (by omega))
  obtain ⟨yst', hbody, hrep, hN', hkeep, haw', henv'⟩ :=
    amProcFrag_correct (dst := dst) (src := src) (l := l) (n := n) (m := m)
      (x := x) (y := y) (cont := [.dynJump] ++ tail) (σ := .code lret :: σ)
      (yst := S₁)
      hAdd hSubStart hSub hSel hDoCopy hCopy hDone hn hn32 hN₁ hawS₁ hdstN hsrcN
      hmodDst hmodSrc hds hsubcDst hsubcSrc hADST₁ hASRC₁ hm₁ hm0 hx₁ hxm hy₁ hym
  have hs4 : ASteps prog ⟨[.dynJump] ++ tail, .code lret :: σ, yst'⟩
      ⟨cont, σ, yst'⟩ :=
    ASteps.single (astep_dynJump hfindRet)
  refine ⟨yst', (((hs1.trans hs2).trans hs3).trans hbody).trans hs4, hrep, hN',
    ?_, ?_, ?_⟩
  · -- preservation: the two call stores plus the body's write set
    intro a ha1 ha2 ha3
    have hbody8 : yst'.memory a = S₁.memory a := by
      refine hkeep a ha1 ha2 ?_
      intro c hc
      have hc' : c ∈ addModCallScratch := by
        unfold addModCallScratch
        exact List.Mem.tail _ (List.Mem.tail _ hc)
      exact ha3 c hc'
    rw [hbody8, hS₁mem]
    rw [storeWord_other (ha3 ASRC (by unfold addModCallScratch; decide)),
      storeWord_other (ha3 ADST (by unfold addModCallScratch; decide))]
  · -- activeWords: the two pinned stores and the body leave it unchanged
    have hawSa' : Sa.activeWords = yst.activeWords := rfl
    have hawS₁' : S₁.activeWords = yst.activeWords := rfl
    rw [haw', hawS₁']
  · -- env unchanged
    have henvS₁ : S₁.env = yst.env := rfl
    rw [henv', henvS₁]

end Challenge.Modexp.Submission.Proof.AddModProcProof
