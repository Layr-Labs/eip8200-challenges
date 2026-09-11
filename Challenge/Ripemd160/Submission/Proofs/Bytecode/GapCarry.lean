import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneCarryAdd

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GapCarry
open PairedLaneCore

theorem add_small_no_carry128 (x : BitVec 128) (e : Nat)
    (he : e < 2 ^ 63) (hgap : x.getLsbD 64 = false) :
    x.toNat + e < 2 ^ 128 := by
  have hx := x.isLt
  have hbit : ¬ x.toNat / 2 ^ 64 % 2 = 1 := by
    simpa only [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq,
      decide_eq_false_iff_not] using hgap
  simp only [Nat.reducePow] at *
  omega

theorem high_add_general (x y : Nat)
    (hcarry : x % 2 ^ 128 + y % 2 ^ 128 < 2 ^ 128) :
    ((x + y) % 2 ^ 256) / 2 ^ 128 % 2 ^ 32 =
      (x / 2 ^ 128 % 2 ^ 32 + y / 2 ^ 128 % 2 ^ 32) % 2 ^ 32 := by
  simp only [Nat.reducePow] at *
  omega

theorem normalize_add_gap (x y : BitVec 256)
    (hy : y.toNat % 2 ^ 128 < 2 ^ 63) (hgap : x.getLsbD 64 = false) :
    normalize (x + y) = normalize (normalize x + y) := by
  have hgap' : (x.extractLsb' 0 128).getLsbD 64 = false := by
    simpa only [BitVec.getLsbD_extractLsb', Nat.zero_add,
      show decide (64 < 128) = true from rfl, Bool.true_and] using hgap
  have hcarry : x.toNat % 2 ^ 128 + y.toNat % 2 ^ 128 < 2 ^ 128 := by
    simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using
      add_small_no_carry128 (x.extractLsb' 0 128) (y.toNat % 2 ^ 128) hy hgap'
  have hnorm : (normalize x).toNat % 2 ^ 128 < 2 ^ 32 := by
    rw [normalize, pack_toNat]
    have hlo := (low x).isLt
    simp only [Nat.reducePow] at *
    omega
  have hcarry' : (normalize x).toNat % 2 ^ 128 + y.toNat % 2 ^ 128 < 2 ^ 128 := by
    simp only [Nat.reducePow] at *
    omega
  have hlo : low (x + y) = low (normalize x + y) := by
    change (x + y).extractLsb' 0 32 = (normalize x + y).extractLsb' 0 32
    rw [BitVec.extractLsb'_add (by decide), BitVec.extractLsb'_add (by decide)]
    change low x + low y = low (pack (low x) (high x)) + low y
    rw [low_pack]
  have hhi : high (x + y) = high (normalize x + y) := by
    apply BitVec.eq_of_toNat_eq
    simp only [high, BitVec.extractLsb'_toNat, BitVec.toNat_add,
      Nat.shiftRight_eq_div_pow]
    rw [high_add_general _ _ hcarry, high_add_general _ _ hcarry']
    have hn : (normalize x).toNat / 2 ^ 128 % 2 ^ 32 = x.toNat / 2 ^ 128 % 2 ^ 32 := by
      have h := congrArg BitVec.toNat (high_pack (low x) (high x))
      simpa only [high, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, normalize] using h
    rw [hn]
  change pack (low (x + y)) (high (x + y)) = pack (low (normalize x + y)) (high (normalize x + y))
  rw [hlo, hhi]

#print axioms normalize_add_gap
end Challenge.Ripemd160.Submission.Proofs.Bytecode.GapCarry
