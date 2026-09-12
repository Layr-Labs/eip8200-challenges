import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerWord
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalar
open EvmSemantics PairedLaneUInt256Bridge Paired80Core Paired80Boolean Paired80Product
open Paired80RoundSemantic Paired80WordRound Paired80WordBoolean Paired80WordRotate

def mask (x : BitVec 256) : BitVec 256 := x &&& lowerMask

theorem mask_eq (x : BitVec 256) : mask x = pack (low x) 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [mask, lowerMask, low, pack, BitVec.getLsbD_and, BitVec.getLsbD_append,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', BitVec.getLsbD_allOnes,
    BitVec.getLsbD_zero, Nat.zero_add, Bool.and_false]
  by_cases h : i < 80
  · simp only [h, ite_true, decide_true, Bool.true_and, Bool.and_comm]
  · simp only [h, ite_false, Bool.and_false]

theorem low_add (x y : BitVec 256) : low (x + y) = low x + low y :=
  BitVec.setWidth_add x y (by decide)

theorem low_mask (x : BitVec 256) : low (mask x) = low x := by rw [mask_eq, low_pack]
theorem mask_clean (x : BitVec 256) : mask (mask x) = mask x := by rw [mask_eq, low_mask, ← mask_eq]
theorem mask_pack (x : BitVec 32) : mask (pack x 0#32) = pack x 0#32 := by rw [mask_eq, low_pack]

def rawF (j : Nat) (b c d : BitVec w) : BitVec w :=
  match j with
  | 0 => b ^^^ c ^^^ d
  | 1 => d ^^^ (b &&& (c ^^^ d))
  | 2 => (b ||| ~~~c) ^^^ d
  | 3 => c ^^^ (d &&& (b ^^^ c))
  | _ => b ^^^ (c ||| ~~~d)

theorem rawF_eq (j : Nat) (b c d : BitVec w) :
    rawF j b c d = f j (BitVec.allOnes w) b c d := by
  rcases Nat.lt_or_ge j 4 with hj | hj
  · interval_cases j <;> simp only [rawF, f, BitVec.xor_allOnes]
    all_goals ac_rfl
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [Nat.add_comm 4 n, rawF, f, BitVec.xor_allOnes]
    ac_rfl

theorem low_rawF (j : Nat) (b c d : BitVec 256) :
    low (rawF j b c d) = f j (BitVec.allOnes 32) (low b) (low c) (low d) := by
  rw [← rawF_eq]
  rcases Nat.lt_or_ge j 4 with hj | hj
  · interval_cases j <;> simp only [rawF, low, BitVec.extractLsb'_xor,
      BitVec.extractLsb'_and, BitVec.extractLsb'_or, BitVec.extractLsb'_not_of_lt (by decide : 0 + 32 < 256)]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
    simp only [Nat.add_comm 4 n, rawF, low, BitVec.extractLsb'_xor,
      BitVec.extractLsb'_and, BitVec.extractLsb'_or, BitVec.extractLsb'_not_of_lt (by decide : 0 + 32 < 256)]

def sum (j : Nat) (a b c d message k : BitVec 256) : BitVec 256 :=
  mask (((a + rawF j b c d) + message) + k)

theorem sum_eq (j : Nat) (a b c d message k : BitVec 256) :
    sum j a b c d message k = pack
      (scalarSum j (low a) (low b) (low c) (low d) (low message) (low k)) 0#32 := by
  simp only [sum, mask_eq, low_add, low_rawF, scalarSum]

def t (maskB : Bool) (j r : Nat) (message k : BitVec 256) (q : Lane 256) : BitVec 256 :=
  let raw := ((sum j q.a q.b q.c q.d message k * factor) >>> (32 - r)) + q.e
  if maskB then mask raw else raw

def step (maskB maskD : Bool) (j r : Nat) (message k : BitVec 256) (q : Lane 256) : Lane 256 :=
  ⟨q.e, t maskB j r message k q, q.b,
    if maskD then mask ((q.c * factor) >>> 22) else (q.c * factor) >>> 22, q.d⟩

def project (q : Lane 256) : Lane 32 := ⟨low q.a, low q.b, low q.c, low q.d, low q.e⟩

def Clean (q : Lane 256) : Prop := mask q.a = q.a ∧ mask q.b = q.b ∧
  mask q.c = q.c ∧ mask q.d = q.d ∧ mask q.e = q.e

theorem low_t (maskB : Bool) (j r : Nat) (hr0 : 0 < r) (hr : r < 32)
    (message k : BitVec 256) (q : Lane 256) :
    low (t maskB j r message k q) = scalarT j r
      (low q.a) (low q.b) (low q.c) (low q.d) (low q.e) (low message) (low k) := by
  cases maskB <;> simp only [t, Bool.false_eq_true, ite_false, ite_true,
    low_mask, low_add, sum_eq, Paired80Rotate.low_rotate_product _ _ r hr0 hr, scalarT]

theorem project_step (maskB maskD : Bool) (j r : Nat) (hr0 : 0 < r) (hr : r < 32)
    (message k : BitVec 256) (q : Lane 256) (hc : mask q.c = q.c) :
    project (step maskB maskD j r message k q) =
      scalarStep j r (low message) (low k) (project q) := by
  have hqc : q.c = pack (low q.c) 0#32 := hc.symm.trans (mask_eq q.c)
  simp only [project, step, scalarStep, low_t maskB j r hr0 hr]
  congr 1
  rw [hqc]
  cases maskD <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    low_mask, show 22 = 32 - 10 from rfl,
    Paired80Rotate.low_rotate_product _ _ 10 (by decide) (by decide), low_pack]

theorem step_b_clean (maskD : Bool) (j r : Nat) (message k : BitVec 256) (q : Lane 256) :
    mask (step true maskD j r message k q).b = (step true maskD j r message k q).b := by
  exact mask_clean _

theorem step_clean (j r : Nat) (message k : BitVec 256) (q : Lane 256) (hq : Clean q) :
    Clean (step true true j r message k q) := by
  exact ⟨hq.2.2.2.2, mask_clean _, hq.2.1, mask_clean _, hq.2.2.2.1⟩

#print axioms mask_eq
#print axioms low_rawF
#print axioms project_step
#print axioms step_clean
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScalar
