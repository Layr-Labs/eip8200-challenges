import Challenge.EvmProof.Word
set_option warningAsError true
/-!
# SHA-256 operations as EVM word expressions

These definitions mirror the arithmetic/bitwise expressions implemented by
the reference bytecode.  The theorems identify them with the corresponding
operations in `EvmSemantics.Crypto.Sha256`; later symbolic-execution proofs
can therefore rewrite an opcode block to the high-level specification in one
step.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.Word

open EvmSemantics
open Challenge.EvmProof.Word

abbrev EWord := EvmSemantics.UInt256

def evmRotr32 (x : EWord) (n : Nat) : EWord :=
  mask32 (UInt256.shiftRight x (UInt256.ofNat n) |||
    UInt256.shiftLeft x (UInt256.ofNat (32 - n)))

private theorem shiftLeft_toNat (value : UInt256) {shift : Nat}
    (hshift : shift < 256) :
    (UInt256.shiftLeft value (UInt256.ofNat shift)).toNat =
      (value.toNat <<< shift) % 2 ^ 256 := by
  have hs : (UInt256.ofNat shift).toNat = shift := by
    rw [word_toNat_ofNat, Nat.mod_eq_of_lt (by omega : shift < 2 ^ 256)]
  unfold UInt256.shiftLeft
  rw [if_neg (by omega), word_toNat_ofNat, hs]
  rw [show UInt256.size = 2 ^ 256 by rfl, Nat.mod_mod]

private theorem rotrDuplicateNat (x n : Nat) (hn : n ≤ 32) :
    (((x ||| ((x <<< 32) % 2 ^ 256)) >>> n) % 2 ^ 32) =
      (((x >>> n) ||| ((x <<< (32 - n)) % 2 ^ 256)) % 2 ^ 32) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · simp only [decide_true, hi, Bool.true_and, Nat.testBit_shiftRight,
      Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
    have hni : n + i < 256 := by omega
    have hi256 : i < 256 := by omega
    rw [show decide (n + i < 256) = true by simp [hni], Bool.true_and]
    by_cases hwrap : 32 ≤ n + i
    · have hsub : n + i - 32 = i - (32 - n) := by omega
      have hge : 32 - n ≤ i := by omega
      rw [show decide (n + i ≥ 32) = true by simp [hwrap], Bool.true_and,
        show decide (i ≥ 32 - n) = true by simp [hge], Bool.true_and,
        show decide (i < 256) = true by simp [hi256], Bool.true_and, hsub]
    · have hlt : n + i < 32 := by omega
      have hlt' : i < 32 - n := by omega
      rw [show decide (n + i ≥ 32) = false by simp [hlt], Bool.false_and,
        Bool.or_false, show decide (i ≥ 32 - n) = false by
          have hnot : ¬ i ≥ 32 - n := by omega
          simp [hnot],
        Bool.false_and, show decide (i < 256) = true by simp [hi256],
        Bool.true_and, Bool.or_false]
  · simp [hi]

/-- A single duplicated 64-bit lane computes the same low-32-bit rotate as
the compiler's separate left and right shifts. -/
theorem evmRotr32_duplicate (x : UInt256) (n : Nat) (hn : n ≤ 32) :
    mask32 (UInt256.shiftRight
      (UInt256.shiftLeft x (UInt256.ofNat 32) ||| x)
      (UInt256.ofNat n)) = evmRotr32 x n := by
  unfold evmRotr32
  apply word_ext
  rw [mask32_toNat, mask32_toNat]
  rw [show 0xffffffff = 2 ^ 32 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [shiftRight_toNat
    (UInt256.shiftLeft x (UInt256.ofNat 32) ||| x) (by omega : n < 256)]
  change
    ((UInt256.lor (UInt256.shiftLeft x (UInt256.ofNat 32)) x).toNat >>> n) %
        2 ^ 32 =
      (UInt256.lor (UInt256.shiftRight x (UInt256.ofNat n))
        (UInt256.shiftLeft x (UInt256.ofNat (32 - n)))).toNat % 2 ^ 32
  rw [word_toNat_lor, word_toNat_lor]
  rw [shiftRight_toNat x (by omega : n < 256),
    shiftLeft_toNat x (by omega : 32 < 256),
    shiftLeft_toNat x (by omega : 32 - n < 256)]
  rw [Nat.or_comm ((x.toNat <<< 32) % 2 ^ 256) x.toNat]
  exact rotrDuplicateNat x.toNat n hn

def evmCh (x y z : EWord) : EWord :=
  z ^^^ (x &&& (y ^^^ z))

def evmMaj (x y z : EWord) : EWord :=
  (z &&& (y ||| x)) ||| (x &&& y)

def evmSmallSigma0 (x : EWord) : EWord :=
  (evmRotr32 x 7 ^^^ evmRotr32 x 18) ^^^
    UInt256.shiftRight x (UInt256.ofNat 3)

def evmSmallSigma1 (x : EWord) : EWord :=
  (evmRotr32 x 17 ^^^ evmRotr32 x 19) ^^^
    UInt256.shiftRight x (UInt256.ofNat 10)

def evmBigSigma0 (x : EWord) : EWord :=
  (evmRotr32 x 2 ^^^ evmRotr32 x 13) ^^^ evmRotr32 x 22

def evmBigSigma1 (x : EWord) : EWord :=
  (evmRotr32 x 6 ^^^ evmRotr32 x 11) ^^^ evmRotr32 x 25

@[simp] theorem evmRotr32_ofUInt32 (x : UInt32) (n : Nat)
    (hn0 : 0 < n) (hn : n < 32) :
    evmRotr32 (ofUInt32 x) n =
      ofUInt32 (Crypto.Sha256.rotr32 x n) := by
  exact Challenge.EvmProof.Word.evm_rotr32 x n hn0 hn

@[simp] theorem evmCh_ofUInt32 (x y z : UInt32) :
    evmCh (ofUInt32 x) (ofUInt32 y) (ofUInt32 z) =
      ofUInt32 (Crypto.Sha256.Ch x y z) := by
  unfold evmCh
  rw [← ofUInt32_xor, ← ofUInt32_and, ← ofUInt32_xor]
  apply congrArg ofUInt32
  rw [← UInt32.toBitVec_inj]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hall : (4294967295#32) = BitVec.allOnes 32 := by decide
  have hbit : (4294967295#32)[i] = true := by
    simpa only [hall] using BitVec.getElem_allOnes i hi
  simp [Crypto.Sha256.Ch]
  rw [hbit]
  generalize x.toBitVec[i] = xb
  generalize y.toBitVec[i] = yb
  generalize z.toBitVec[i] = zb
  cases xb <;> cases yb <;> cases zb <;> decide

@[simp] theorem evmMaj_ofUInt32 (x y z : UInt32) :
    evmMaj (ofUInt32 x) (ofUInt32 y) (ofUInt32 z) =
      ofUInt32 (Crypto.Sha256.Maj x y z) := by
  unfold evmMaj
  rw [← ofUInt32_or, ← ofUInt32_and, ← ofUInt32_and, ← ofUInt32_or]
  apply congrArg ofUInt32
  rw [← UInt32.toBitVec_inj]
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp [Crypto.Sha256.Maj]
  generalize x.toBitVec[i] = xb
  generalize y.toBitVec[i] = yb
  generalize z.toBitVec[i] = zb
  cases xb <;> cases yb <;> cases zb <;> decide

@[simp] theorem evmSmallSigma0_ofUInt32 (x : UInt32) :
    evmSmallSigma0 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.smallSigma0 x) := by
  unfold evmSmallSigma0 Crypto.Sha256.smallSigma0 Crypto.Sha256.shr32
  rw [evmRotr32_ofUInt32 x 7 (by decide) (by decide),
    evmRotr32_ofUInt32 x 18 (by decide) (by decide),
    shiftRight_ofUInt32 x 3 (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmSmallSigma1_ofUInt32 (x : UInt32) :
    evmSmallSigma1 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.smallSigma1 x) := by
  unfold evmSmallSigma1 Crypto.Sha256.smallSigma1 Crypto.Sha256.shr32
  rw [evmRotr32_ofUInt32 x 17 (by decide) (by decide),
    evmRotr32_ofUInt32 x 19 (by decide) (by decide),
    shiftRight_ofUInt32 x 10 (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmBigSigma0_ofUInt32 (x : UInt32) :
    evmBigSigma0 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.bigSigma0 x) := by
  unfold evmBigSigma0 Crypto.Sha256.bigSigma0
  rw [evmRotr32_ofUInt32 x 2 (by decide) (by decide),
    evmRotr32_ofUInt32 x 13 (by decide) (by decide),
    evmRotr32_ofUInt32 x 22 (by decide) (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

@[simp] theorem evmBigSigma1_ofUInt32 (x : UInt32) :
    evmBigSigma1 (ofUInt32 x) =
      ofUInt32 (Crypto.Sha256.bigSigma1 x) := by
  unfold evmBigSigma1 Crypto.Sha256.bigSigma1
  rw [evmRotr32_ofUInt32 x 6 (by decide) (by decide),
    evmRotr32_ofUInt32 x 11 (by decide) (by decide),
    evmRotr32_ofUInt32 x 25 (by decide) (by decide),
    ← ofUInt32_xor, ← ofUInt32_xor]

end Challenge.Sha256.Submission.Proofs.Bytecode.Word
