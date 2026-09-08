import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedF

open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLaneMask

/-! The packed Boolean expression has a left lane in bits 0--31 and a right
lane in bits 64--95.  The masks select `f r` on the left and `f (4-r)` on the
right.  These lemmas are purely about `Nat` bits; they do not depend on an EVM
trace or on a concrete bytecode artifact. -/

def boolF (j : Nat) (x y z : Bool) : Bool :=
  match j with
  | 0 => xor (xor x y) z
  | 1 => (x && y) || (!x && z)
  | 2 => xor (x || !y) z
  | 3 => (x && z) || (y && !z)
  | _ => xor x (y || !z)

def natPackedF (r : Nat) (x y z : Nat) : Nat :=
  match r with
  | 0 => ((x ^^^ y) ^^^ maskRN) ^^^ ((y &&& maskRN) ||| z)
  | 1 => (((y ^^^ z) &&& x) ^^^ z) ^^^
      (((x &&& y) ^^^ (y ||| z)) &&& maskRN)
  | 2 => ((y ^^^ maskLRN) ||| x) ^^^ z
  | 3 => (((x ^^^ y) &&& z) ^^^ y) ^^^
      (((x &&& y) ^^^ (y ||| z)) &&& maskRN)
  | _ => ((x ^^^ y) ^^^ maskLN) ^^^ ((y &&& maskLN) ||| z)

def natF (j : Nat) (x y z : Nat) : Nat :=
  match j with
  | 0 => (x ^^^ y) ^^^ z
  | 1 => (x &&& y) ||| ((maskLN ^^^ x) &&& z)
  | 2 => (x ||| (maskLN ^^^ y)) ^^^ z
  | 3 => (x &&& z) ||| (y &&& (maskLN ^^^ z))
  | _ => x ^^^ (y ||| (maskLN ^^^ z))

private theorem testBit_natF (j x y z i : Nat) (hj : j < 5) (hi : i < 32) :
    (natF j x y z).testBit i =
      boolF j (x.testBit i) (y.testBit i) (z.testBit i) := by
  interval_cases j <;>
    simp [natF, boolF, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      testBit_maskLN, hi]

private theorem testBit_natPackedF_lane0 (r x y z i : Nat)
    (hr : r < 5) (hi : i < 32) :
    (natPackedF r x y z).testBit i =
      boolF r (x.testBit i) (y.testBit i) (z.testBit i) := by
  have hi64 : ¬64 ≤ i := by omega
  interval_cases r <;>
    simp [natPackedF, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      testBit_maskLN, testBit_maskRN, testBit_maskLRN, hi, hi64]
  all_goals
    generalize x.testBit i = xb
    generalize y.testBit i = yb
    generalize z.testBit i = zb
    revert xb yb zb
    decide

private theorem testBit_natPackedF_lane1 (r x y z i : Nat)
    (hr : r < 5) (hi : i < 32) :
    (natPackedF r x y z).testBit (64 + i) =
      boolF (4 - r) (x.testBit (64 + i)) (y.testBit (64 + i))
        (z.testBit (64 + i)) := by
  have h64 : 64 ≤ 64 + i := by omega
  have hsub : 64 + i - 64 = i := by omega
  have hnotlow : ¬64 + i < 32 := by omega
  interval_cases r <;>
    simp [natPackedF, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      testBit_maskLN, testBit_maskRN, testBit_maskLRN, hi, h64, hsub,
      hnotlow]
  all_goals
    generalize x.testBit (64 + i) = xb
    generalize y.testBit (64 + i) = yb
    generalize z.testBit (64 + i) = zb
    revert xb yb zb
    decide

/-- Lane 0 of the packed Boolean expression is the left RIPEMD line's
Boolean function for round group `r`. -/
theorem packedF_lane0 (r x y z : Nat) (hr : r < 5) :
    lane0N (natPackedF r x y z) =
      natF r (lane0N x) (lane0N y) (lane0N z) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · rw [testBit_natF _ _ _ _ _ hr hi]
    simp only [lane0N, testBit_windowN, hi, decide_true, Bool.true_and]
    simpa only [Nat.zero_add] using testBit_natPackedF_lane0 r x y z i hr hi
  · simp only [lane0N, testBit_windowN, hi, decide_false, Bool.false_and]
    interval_cases r <;>
      simp [natF, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        testBit_windowN, testBit_maskLN, hi]

/-- Lane 1 of the packed Boolean expression is the right RIPEMD line's
Boolean function, whose round groups run in the reverse order. -/
theorem packedF_lane1 (r x y z : Nat) (hr : r < 5) :
    lane1N (natPackedF r x y z) =
      natF (4 - r) (lane1N x) (lane1N y) (lane1N z) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 32
  · rw [testBit_natF _ _ _ _ _ (by omega) hi]
    simp only [lane1N, testBit_windowN, hi, decide_true, Bool.true_and]
    exact testBit_natPackedF_lane1 r x y z i hr hi
  · simp only [lane1N, testBit_windowN, hi, decide_false, Bool.false_and]
    interval_cases r <;>
      simp [natF, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
        testBit_windowN, testBit_maskLN, hi]

#print axioms packedF_lane0
#print axioms packedF_lane1

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedF
