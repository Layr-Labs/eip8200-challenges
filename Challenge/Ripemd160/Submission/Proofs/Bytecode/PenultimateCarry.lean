import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneScaledRotate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCarryAdd

set_option warningAsError true
set_option maxHeartbeats 200000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateCarry
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open PairedLaneCore PairedLaneProduct PairedLaneScaledRotate PairedLaneCarry

theorem add64_no_carry128 (x : BitVec 128) (e : BitVec 64)
    (hgap : x.getLsbD 64 = false) : x.toNat + e.toNat < 2 ^ 128 := by
  have hx := x.isLt
  have he := e.isLt
  have hbit : ¬ x.toNat / 2 ^ 64 % 2 = 1 := by
    simpa only [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not] using hgap
  simp only [Nat.reducePow] at *
  omega

private theorem spacer101 (x y : Nat) (hx : x < 2 ^ 64) :
    (x + y * 2 ^ 101).testBit 64 = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq,
    div_pow_add_mul_pow x y 64 101 (by decide), Nat.div_eq_of_lt hx, Nat.zero_add]
  simp [Nat.mul_mod]

theorem raw78_added_gap (a b e f : BitVec 32) :
    (((scaleHigh (pack a b) 6 * factor) >>> 27) + pack e f).getLsbD 64 = false := by
  let x := a.toNat * (2 ^ 32 + 1) / 2 ^ 27 + e.toNat
  let y := b.toNat * (2 ^ 32 + 1) * 2 ^ 6 + f.toNat * 2 ^ 27
  have he := e.isLt
  have ha := aF_lt_64 a
  have hx : x < 2 ^ 64 := by
    dsimp [x]
    simp only [Nat.reducePow] at *
    omega
  have hvalue :
      ((((scaleHigh (pack a b) 6 * factor) >>> 27) + pack e f).toNat) =
        (x + y * 2 ^ 101) % 2 ^ 256 := by
    rw [BitVec.toNat_add, toNat_shift, scaleHigh_product_toNat a b 6 (by decide),
      div_pow_add_mul_pow _ _ 27 128 (by decide), PairedLaneCore.pack_toNat]
    congr 1
    dsimp [x, y]
    ring
  rw [← BitVec.testBit_toNat, hvalue, Nat.testBit_mod_two_pow]
  simpa using spacer101 x y hx

theorem raw_c10_gap (a b : BitVec 32) :
    ((pack a b * factor) >>> 22).getLsbD 64 = false := by
  exact shifted_product_gap a b 10 (by decide) (by decide)

theorem high_add_three_pack_nat (n al ar bl br cl cr : Nat)
    (hgap : n.testBit 64 = false)
    (ha : al < 2 ^ 32) (hb : bl < 2 ^ 32) (hc : cl < 2 ^ 32) :
    (((((n + (al + 2 ^ 128 * ar)) % 2 ^ 256 +
        (bl + 2 ^ 128 * br)) % 2 ^ 256 +
        (cl + 2 ^ 128 * cr)) % 2 ^ 256) / 2 ^ 128) % 2 ^ 32 =
      (n / 2 ^ 128 % 2 ^ 32 + ar + br + cr) % 2 ^ 32 := by
  have hbit : ¬ n / 2 ^ 64 % 2 = 1 := by
    simpa only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_false_iff_not] using hgap
  simp only [Nat.reducePow] at *
  omega

#print axioms raw78_added_gap
#print axioms raw_c10_gap
#print axioms high_add_three_pack_nat

theorem normalize_three_add (x : BitVec 256) (al ar bl br cl cr : BitVec 32)
    (hgap : x.getLsbD 64 = false) :
    normalize (((x + pack al ar) + pack bl br) + pack cl cr) =
      pack (low x + al + bl + cl) (high x + ar + br + cr) := by
  have hlo : low (((x + pack al ar) + pack bl br) + pack cl cr) =
      low x + al + bl + cl := by
    change (((x + pack al ar) + pack bl br) + pack cl cr).extractLsb' 0 32 = _
    rw [BitVec.extractLsb'_add (by decide), BitVec.extractLsb'_add (by decide),
      BitVec.extractLsb'_add (by decide)]
    change low x + low (pack al ar) + low (pack bl br) + low (pack cl cr) = _
    simp only [low_pack]
  have hhi : high (((x + pack al ar) + pack bl br) + pack cl cr) =
      high x + ar + br + cr := by
    apply BitVec.eq_of_toNat_eq
    have hp (a b : BitVec 32) : (pack a b).toNat = a.toNat + 2 ^ 128 * b.toNat := by
      rw [pack_toNat, Nat.mul_comm b.toNat]
    simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_add, hp,
      Nat.shiftRight_eq_div_pow]
    have h := high_add_three_pack_nat x.toNat al.toNat ar.toNat bl.toNat br.toNat
      cl.toNat cr.toNat (by simpa only [BitVec.testBit_toNat] using hgap)
      al.isLt bl.isLt cl.isLt
    simpa only [Nat.add_mod, Nat.mod_mod] using h
  exact congr (congrArg pack hlo) hhi

theorem normalize_three_add_congr (x y : BitVec 256) (al ar bl br cl cr : BitVec 32)
    (hx : x.getLsbD 64 = false) (hy : y.getLsbD 64 = false)
    (hxy : normalize x = normalize y) :
    normalize (((x + pack al ar) + pack bl br) + pack cl cr) =
      normalize (((y + pack al ar) + pack bl br) + pack cl cr) := by
  have h := pack_injective hxy
  rw [normalize_three_add x al ar bl br cl cr hx,
    normalize_three_add y al ar bl br cl cr hy, h.1, h.2]

def boolean4 (b c d : BitVec 256) : BitVec 256 :=
  (PairedLaneBoolean.lowerMask &&& (d ||| ~~~c)) ^^^ (d ^^^ (c ^^^ b))

theorem boolean4_normalize_bd (b c d : BitVec 256) :
    normalize (boolean4 b c d) = normalize (boolean4 (normalize b) c (normalize d)) := by
  simp only [normalize_eq_and, boolean4]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hi, decide_true, Bool.true_and]
  cases pairMask.getLsbD i <;> cases PairedLaneBoolean.lowerMask.getLsbD i <;>
    cases b.getLsbD i <;> cases c.getLsbD i <;> cases d.getLsbD i <;> rfl

theorem boolean4_gap (b c d : BitVec 256)
    (hb : b.getLsbD 64 = false) (hc : c.getLsbD 64 = false)
    (hd : d.getLsbD 64 = false) : (boolean4 b c d).getLsbD 64 = false := by
  simp only [boolean4, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_or,
    BitVec.getLsbD_not, hb, hc, hd,
    show PairedLaneBoolean.lowerMask.getLsbD 64 = false by decide]
  rfl

theorem normalize_gap (x : BitVec 256) : (normalize x).getLsbD 64 = false := by
  rw [normalize_eq_and, BitVec.getLsbD_and]
  exact Bool.and_false _

#print axioms normalize_three_add
#print axioms normalize_three_add_congr
#print axioms boolean4_normalize_bd
#print axioms boolean4_gap
#print axioms normalize_gap
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PenultimateCarry

