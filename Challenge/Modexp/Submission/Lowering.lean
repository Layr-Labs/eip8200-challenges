import YulEvmCompiler.Compile
set_option warningAsError true

/-!
# Kernel-reducible lowering bridge

The pinned compiler's lowering chain (`lowerProg`) does not evaluate in the
Lean kernel: `Instr.byteWidth` is well-founded-recursive, and well-founded
recursion is opaque to kernel reduction, so `decide` cannot produce the
`lowerProg prog = some is` fact that `YulEvmCompiler.arun_halt_sim` consumes.

This module re-implements the byte-width computation as a structural
fuel-bounded probe loop (`byteWidth'`), proves it equals `Instr.byteWidth` on
every 256-bit value using only the packaged order lemmas
(`Instr.lt_pow_byteWidth`, `Instr.byteWidth_le_of_lt_pow`), and mirrors the
whole lowering chain (`size'`, `codeSize'`, `resolve'`, `lowerInstr'`,
`lowerFrag'`, `lowerProg'`) with the structural variant. Pointwise equalities
lift to `lowerProg prog = lowerProg' prog`, and the right-hand side *does*
reduce in the kernel, so `lowerProg prog = some is` is proved by rewriting
plus `decide`.
-/

namespace Challenge.Modexp.Submission

open YulEvmCompiler
open EvmSemantics (UInt256)
open YulSemantics.EVM (U256)

/-- Probe loop: the least `e` in `[e₀, 32]` with `n < 256^e`, else 32.
Structural recursion on `fuel`, so the kernel evaluates it. -/
def byteWidthLoop (n e fuel : Nat) : Nat :=
  match fuel with
  | 0 => 32
  | fuel + 1 => if n < 256^e then e else byteWidthLoop n (e + 1) fuel

/-- Structural byte width: for `n < 256^32`, the least `w` with `n < 256^w`
(`0` for `n = 0`). Unlike `Instr.byteWidth` the kernel computes it. -/
def byteWidth' (n : Nat) : Nat := byteWidthLoop n 0 32

/-- The probe loop never exceeds 32. -/
theorem byteWidthLoop_le (n : Nat) :
    ∀ fuel e, e + fuel = 32 → byteWidthLoop n e fuel ≤ 32 := by
  intro fuel
  induction fuel with
  | zero => intro e _; simp [byteWidthLoop]
  | succ fuel ih =>
    intro e hef
    unfold byteWidthLoop
    split
    · omega
    · exact ih (e + 1) (by omega)

/-- `byteWidth'` never exceeds 32. -/
theorem byteWidth'_le_32 (n : Nat) : byteWidth' n ≤ 32 :=
  byteWidthLoop_le n 32 0 rfl

/-- Specification of the probe loop: at every reachable state the result is a
power of 256 strictly above `n`, with the previous power at most `n`. -/
theorem byteWidthLoop_spec {n : Nat} (h : n < 256^32) :
    ∀ fuel e, e + fuel = 32 → (e = 0 ∨ 256^(e-1) ≤ n) →
      n < 256 ^ byteWidthLoop n e fuel ∧
        (0 < byteWidthLoop n e fuel → 256 ^ (byteWidthLoop n e fuel - 1) ≤ n) := by
  intro fuel
  induction fuel with
  | zero =>
    intro e hef hpre
    simp only [byteWidthLoop]
    have : e = 32 := by omega
    subst this
    constructor
    · exact h
    · intro _
      rcases hpre with h0 | hle
      · omega
      · simpa using hle
  | succ fuel ih =>
    intro e hef hpre
    unfold byteWidthLoop
    split
    · next hlt =>
      constructor
      · exact hlt
      · intro he
        rcases hpre with h0 | hle
        · omega
        · exact hle
    · next hge =>
      simp only [Nat.not_lt] at hge
      exact ih (e + 1) (by omega) (Or.inr hge)

/-- Specification of `byteWidth'` on 256-bit-range naturals. -/
theorem byteWidth'_spec {n : Nat} (h : n < 256^32) :
    n < 256 ^ byteWidth' n ∧ (0 < byteWidth' n → 256 ^ (byteWidth' n - 1) ≤ n) :=
  byteWidthLoop_spec h 32 0 rfl (Or.inl rfl)

/-- The structural byte width agrees with the well-founded original on every
value below `256^32 = 2^256`. -/
theorem byteWidth_eq_of_lt {n : Nat} (h : n < 256^32) :
    Instr.byteWidth n = byteWidth' n := by
  obtain ⟨hub, hlb⟩ := byteWidth'_spec h
  apply le_antisymm
  · exact Instr.byteWidth_le_of_lt_pow n (byteWidth' n) hub
  · by_cases h0 : byteWidth' n = 0
    · omega
    · have hb := Instr.lt_pow_byteWidth n
      by_contra hlt
      push Not at hlt
      have hle : 256 ^ Instr.byteWidth n ≤ 256 ^ (byteWidth' n - 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have := hlb (by omega)
      omega

/-- `256^32 = 2^256`, mirroring the private fact in `YulEvmCompiler.Instr`. -/
private theorem pow_256_32 : (256 : Nat) ^ 32 = 2 ^ 256 := by
  have h8 : (256 : Nat) = 2 ^ 8 := by decide
  calc (256 : Nat) ^ 32 = (2 ^ 8) ^ 32 := by rw [h8]
    _ = 2 ^ (8 * 32) := (Nat.pow_mul 2 8 32).symm
    _ = 2 ^ 256 := rfl

/-- `byteWidth'` agrees with `Instr.byteWidth` on machine words. -/
theorem byteWidth_eq_word (v : UInt256) :
    Instr.byteWidth v.toNat = byteWidth' v.toNat :=
  byteWidth_eq_of_lt (by rw [pow_256_32]; exact v.val.isLt)

/-- Structural minimal push width (kernel-evaluable). -/
def widthOf' (v : UInt256) : Fin 33 :=
  ⟨byteWidth' v.toNat, by have := byteWidth'_le_32 v.toNat; omega⟩

/-- Structural minimal-width push (kernel-evaluable). -/
def pushMin' (v : UInt256) : Instr := .push (widthOf' v) v

/-- `pushMin'` equals the pinned `Instr.pushMin`. -/
theorem pushMin_eq (v : UInt256) : Instr.pushMin v = pushMin' v := by
  simp only [Instr.pushMin, pushMin', Instr.widthOf, widthOf']
  congr 1
  exact Fin.ext (byteWidth_eq_word v)

/-- Structural `Asm.size`. -/
def size' : Asm → Nat
  | .push v => 1 + byteWidth' (conv v).toNat
  | .op _ => 1
  | .dup _ => 1
  | .swap _ => 1
  | .pop => 1
  | .label _ => 1
  | .jump _ => labelWidth + 2
  | .jumpi _ => labelWidth + 2
  | .pushLabel _ => labelWidth + 1
  | .dynJump => 1

/-- `size'` equals `Asm.size` pointwise. -/
theorem size_eq (i : Asm) : Asm.size i = size' i := by
  cases i
  · simp only [Asm.size, size']; rw [byteWidth_eq_word]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- Structural `codeSize` (pattern-matching, so cons computes by `rfl`). -/
def codeSize' : List Asm → Nat
  | [] => 0
  | i :: p => size' i + codeSize' p

@[simp] theorem codeSize'_nil : codeSize' [] = 0 := rfl
@[simp] theorem codeSize'_cons (i : Asm) (p : List Asm) :
    codeSize' (i :: p) = size' i + codeSize' p := rfl

/-- `codeSize'` equals `codeSize`. -/
theorem codeSize_eq (p : List Asm) : codeSize p = codeSize' p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    rw [codeSize_cons, size_eq i, ih, codeSize'_cons]

/-- Structural label resolution. -/
def resolve' (l : Label) : List Asm → Option Nat
  | [] => none
  | i :: rest =>
    if i = .label l then some 0
    else (resolve' l rest).map (size' i + ·)

/-- `resolve'` equals `resolve`. -/
theorem resolve_eq (l : Label) (p : List Asm) : resolve l p = resolve' l p := by
  induction p with
  | nil => rfl
  | cons i rest ih =>
    simp only [resolve, resolve', size_eq i, ih]

/-- Structural instruction lowering. -/
def lowerInstr' (prog : List Asm) : Asm → Option (List Instr)
  | .push v      => some [pushMin' (conv v)]
  | .op yop      => (opTable yop).map (fun o => [.op o])
  | .dup n       => some [.op (.Dup ⟨n⟩)]
  | .swap n      => some [.op (.Swap ⟨n⟩)]
  | .pop         => some [.op .POP]
  | .label _     => some [.op .JUMPDEST]
  | .jump l      => (resolve' l prog).map
      (fun a => [.push labelWidthFin (UInt256.ofNat a), .op .JUMP])
  | .jumpi l     => (resolve' l prog).map
      (fun a => [.push labelWidthFin (UInt256.ofNat a), .op .JUMPI])
  | .pushLabel l => (resolve' l prog).map
      (fun a => [.push labelWidthFin (UInt256.ofNat a)])
  | .dynJump     => some [.op .JUMP]

/-- `lowerInstr'` equals `lowerInstr`. -/
theorem lowerInstr_eq (prog : List Asm) (i : Asm) :
    lowerInstr prog i = lowerInstr' prog i := by
  cases i <;> simp only [lowerInstr, lowerInstr']
  · rw [pushMin_eq]
  · rw [resolve_eq]
  · rw [resolve_eq]
  · rw [resolve_eq]

/-- Structural fragment lowering. -/
def lowerFrag' (prog : List Asm) : List Asm → Option (List Instr)
  | [] => some []
  | i :: rest => do
      let is1 ← lowerInstr' prog i
      let is2 ← lowerFrag' prog rest
      return is1 ++ is2

/-- `lowerFrag'` equals `lowerFrag`. -/
theorem lowerFrag_eq (prog frag : List Asm) :
    lowerFrag prog frag = lowerFrag' prog frag := by
  induction frag with
  | nil => rfl
  | cons i rest ih =>
    simp only [lowerFrag, lowerFrag', lowerInstr_eq, ih]

/-- Structural whole-program lowering. -/
def lowerProg' (p : List Asm) : Option (List Instr) := lowerFrag' p p

/-- `lowerProg'` equals `lowerProg`; with it, the kernel-checkable `lowerProg'`
witnesses the proof-facing `lowerProg`. -/
theorem lowerProg_eq (p : List Asm) : lowerProg p = lowerProg' p :=
  lowerFrag_eq p p

/-- Produce the proof-facing lowering fact from the kernel-evaluable one. -/
theorem lowerProg_of_lowerProg' {p : List Asm} {is : List Instr}
    (h : lowerProg' p = some is) : lowerProg p = some is := by
  rw [lowerProg_eq]; exact h

/-- Decidable equality on instructions, used to `decide` lowering facts. -/
instance : DecidableEq Instr
  | .push w1 v1, .push w2 v2 =>
    if hw : w1 = w2 then
      if hv : v1 = v2 then isTrue (by subst hw; subst hv; rfl)
      else isFalse (fun h => hv (Instr.push.inj h).2)
    else isFalse (fun h => hw (Instr.push.inj h).1)
  | .op o1, .op o2 =>
    if h : o1 = o2 then isTrue (by subst h; rfl)
    else isFalse (fun he => h (Instr.op.inj he))
  | .push .., .op .. => isFalse (fun h => Instr.noConfusion h)
  | .op .., .push .. => isFalse (fun h => Instr.noConfusion h)

end Challenge.Modexp.Submission
