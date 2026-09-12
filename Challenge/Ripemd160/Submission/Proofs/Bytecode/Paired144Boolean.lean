import Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Core

set_option warningAsError true

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Boolean

open Paired144Core

theorem pack_and (a b c d : BitVec 32) :
    pack a b &&& pack c d = pack (a &&& c) (b &&& d) := by
  unfold pack
  rw [BitVec.and_append (x₁ := b.setWidth 112) (x₂ := d.setWidth 112)
    (y₁ := a.setWidth 144) (y₂ := c.setWidth 144)]
  rw [BitVec.setWidth_and, BitVec.setWidth_and]

theorem pack_or (a b c d : BitVec 32) :
    pack a b ||| pack c d = pack (a ||| c) (b ||| d) := by
  unfold pack
  rw [BitVec.or_append (x₁ := b.setWidth 112) (x₂ := d.setWidth 112)
    (y₁ := a.setWidth 144) (y₂ := c.setWidth 144)]
  rw [BitVec.setWidth_or, BitVec.setWidth_or]

theorem pack_xor (a b c d : BitVec 32) :
    pack a b ^^^ pack c d = pack (a ^^^ c) (b ^^^ d) := by
  unfold pack
  rw [BitVec.xor_append (x₁ := b.setWidth 112) (x₂ := d.setWidth 112)
    (y₁ := a.setWidth 144) (y₂ := c.setWidth 144)]
  rw [BitVec.setWidth_xor, BitVec.setWidth_xor]

theorem pack_complement (a b : BitVec 32) :
    pack a b ^^^ pairMask = pack (~~~a) (~~~b) := by
  rw [pairMask, pack_xor, BitVec.xor_allOnes, BitVec.xor_allOnes]

def upperMask : BitVec 256 := pack 0#32 (BitVec.allOnes 32)
def lowerMask : BitVec 256 := pack (BitVec.allOnes 32) 0#32

theorem blend_pack (a b c d : BitVec 32) :
    pack a b ^^^ ((pack a b ^^^ pack c d) &&& upperMask) = pack a d := by
  simp only [upperMask, pack_xor, pack_and, BitVec.and_zero,
    BitVec.and_allOnes, BitVec.xor_zero, ← BitVec.xor_assoc,
    BitVec.xor_self, BitVec.zero_xor]

/-- Complement is restricted to the two normalized 32-bit cells. -/
def f (j : Nat) (mask b c d : BitVec w) : BitVec w :=
  match j with
  | 0 => (b ^^^ c) ^^^ d
  | 1 => ((c ^^^ d) &&& b) ^^^ d
  | 2 => ((c ^^^ mask) ||| b) ^^^ d
  | 3 => ((b ^^^ c) &&& d) ^^^ c
  | _ => ((d ^^^ mask) ||| c) ^^^ b

theorem f_pack (j : Nat) (a b c d e g : BitVec 32) :
    f j pairMask (pack a b) (pack c d) (pack e g) =
      pack (f j (BitVec.allOnes 32) a c e)
        (f j (BitVec.allOnes 32) b d g) := by
  cases j with
  | zero => simp only [f, pack_xor]
  | succ j => cases j with
    | zero => simp only [f, pack_xor, pack_and]
    | succ j => cases j with
      | zero => simp only [f, pairMask, pack_xor, pack_or]
      | succ j => cases j with
        | zero => simp only [f, pack_xor, pack_and]
        | succ j => simp only [f, pairMask, pack_xor, pack_or]

/-- The single correction shared by the F0/F4 lane pair. -/
theorem f04_correction (b c d : BitVec w) :
    ((b ^^^ c) ^^^ d) ^^^ ((~~~c) ||| d) =
      ((~~~d) ||| c) ^^^ b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

/-- The exact per-group Boolean expressions of the paired assembler. -/
def pairedF (j : Nat) (b c d : BitVec 256) : BitVec 256 :=
  match j with
  | 0 => f 0 pairMask b c d ^^^ (((c ^^^ pairMask) ||| d) &&& upperMask)
  | 1 => f 1 pairMask b c d ^^^
      ((f 1 pairMask b c d ^^^ f 3 pairMask b c d) &&& upperMask)
  | 2 => f 2 pairMask b c d
  | 3 => f 3 pairMask b c d ^^^
      ((f 3 pairMask b c d ^^^ f 1 pairMask b c d) &&& upperMask)
  | _ => f 0 pairMask b c d ^^^ (((c ^^^ pairMask) ||| d) &&& lowerMask)

theorem pairedF_pack (j : Nat) (a b c d e g : BitVec 32) :
    pairedF j (pack a b) (pack c d) (pack e g) =
      pack (f j (BitVec.allOnes 32) a c e)
        (f (4 - j) (BitVec.allOnes 32) b d g) := by
  cases j with
  | zero =>
    simp only [pairedF, Nat.reduceSub]
    simp only [f_pack]
    simp only [upperMask, pairMask, pack_xor,
      pack_or, pack_and, f, BitVec.and_zero, BitVec.and_allOnes,
      BitVec.xor_zero, BitVec.xor_allOnes, f04_correction]
  | succ j => cases j with
    | zero =>
      simp only [pairedF]
      simp only [f_pack, blend_pack]
    | succ j => cases j with
      | zero =>
        exact f_pack 2 a b c d e g
      | succ j => cases j with
        | zero =>
          simp only [pairedF]
          simp only [f_pack, blend_pack]
        | succ j =>
          have hj : 4 - (j + 1 + 1 + 1 + 1) = 0 := by omega
          simp only [pairedF, hj]
          simp only [f_pack]
          simp only [lowerMask, pairMask, pack_xor,
            pack_or, pack_and, f, BitVec.and_zero,
            BitVec.and_allOnes, BitVec.xor_zero,
            BitVec.xor_allOnes, f04_correction]

#print axioms pack_and
#print axioms pack_or
#print axioms pack_xor
#print axioms pack_complement
#print axioms blend_pack
#print axioms f_pack
#print axioms f04_correction
#print axioms pairedF_pack

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Paired144Boolean
