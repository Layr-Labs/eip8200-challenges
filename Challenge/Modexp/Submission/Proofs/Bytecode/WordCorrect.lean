import Challenge.Modexp.Submission.Proofs.Bytecode.WordExit
import Challenge.Modexp.Submission.Proofs.Bytecode.WordFast
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
/-!
# Correctness of the one-word MODEXP arithmetic

DRAFT — this module has never been typechecked.  See RECOVERY.md.

Two bridges, both from `WordFast`:

* the word-at-a-time base Horner loop is `WordFast.baseLoop_correct`, with the
  radix `R = addmod(mod(not 0, m), 1, m)` discharged by
  `WordFast.two_pow_256_mod`;
* one exponent byte as two 4-bit windows is `WordFast.windowByte_spec`, whose
  right-hand side `(acc ^ 256 * b ^ w) % m` is exactly the reference byte step,
  so the rest of the chain up to `Precompile.modPow` is unchanged.

`T[0] = mod(1, m)` matters here: with `Esize = 0` the byte loop never runs and
`T[0]` is returned with no trailing `MULMOD`, so `m = 1` must give `0`.  Both
`WordFast.one_mod_pow` and `WordFast.wordPath_modPow` carry that case.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect

open EvmSemantics
open EvmSemantics.EVM
open Word
open WordLoops
open WordExit

theorem right_mod_mul (a b m : Nat) : (a * (b % m)) % m = (a * b) % m := by
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

theorem expAfter_lt (input : ByteArray) (off m b i acc : Nat) (hm : 0 < m)
    (hacc : acc < m) : WordFast.expAfter input off m b i acc < m := by
  induction i with
  | zero => exact hacc
  | succ i ih =>
      rw [WordFast.expAfter, WordFast.expStep]
      exact Nat.mod_lt _ hm

theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  exact Nat.mod_eq_of_lt a.val.isLt

private theorem modWord_ne (modulus : Nat) (hmodpos : 0 < modulus)
    (hmodlt : modulus < 2 ^ 256) : (UInt256.ofNat modulus).val.val ≠ 0 := by
  change (UInt256.ofNat modulus).toNat ≠ 0
  rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt]
  omega

theorem mulMod_toNat (a b : UInt256) (modulus : Nat)
    (hmodpos : 0 < modulus) (hmodlt : modulus < 2 ^ 256) :
    (UInt256.mulMod a b (UInt256.ofNat modulus)).toNat =
      (a.toNat * b.toNat) % modulus := by
  unfold UInt256.mulMod
  rw [if_neg (modWord_ne modulus hmodpos hmodlt),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmodlt,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

theorem addMod_toNat (a b : UInt256) (modulus : Nat)
    (hmodpos : 0 < modulus) (hmodlt : modulus < 2 ^ 256) :
    (UInt256.addMod a b (UInt256.ofNat modulus)).toNat =
      (a.toNat + b.toNat) % modulus := by
  unfold UInt256.addMod
  rw [if_neg (modWord_ne modulus hmodpos hmodlt),
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hmodlt,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

/-! ## The radix constant -/

theorem radixWord_toNat (input : ByteArray) (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    (radixWord input).toNat = 2 ^ 256 % modulusValue input := by
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  have hlnot : (UInt256.lnot 0).toNat = 2 ^ 256 - 1 := by
    unfold UInt256.lnot
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, hzeroNat]
    norm_num [UInt256.size]
  have hone : (1 : UInt256).toNat = 1 := by decide
  have hmodstep : (UInt256.lnot 0 % UInt256.ofNat (modulusValue input)).toNat =
      (2 ^ 256 - 1) % modulusValue input := by
    change (UInt256.mod (UInt256.lnot 0)
      (UInt256.ofNat (modulusValue input))).toNat = _
    unfold UInt256.mod
    rw [if_neg (modWord_ne _ hmodpos hmodlt)]
    change ((UInt256.lnot 0).val % (UInt256.ofNat (modulusValue input)).val).val = _
    rw [Fin.val_mod]
    change (UInt256.lnot 0).toNat % (UInt256.ofNat (modulusValue input)).toNat = _
    rw [hlnot, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hmodlt]
  unfold radixWord
  rw [addMod_toNat _ _ _ hmodpos hmodlt, hmodstep, hone]
  exact WordFast.two_pow_256_mod (modulusValue input)

/-! ## The base loop -/

theorem readWord_calldata (input : ByteArray) (off : Nat) :
    (MachineState.readWord input off).toNat =
      Precompile.bytesToNatPadded input off 32 := by
  have h : MachineState.readWord input off =
      UInt256.ofNat (Precompile.bytesToNatPadded input off 32) := rfl
  rw [h, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input off 32
      |>.trans_le (by norm_num))]

theorem hornerAfter_toNat (input : ByteArray) (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) (k : Nat) :
    (hornerAfter input k).toNat =
      WordFast.hornerAfter input 96 (leadWidth input) (modulusValue input)
        (radixWord input).toNat k := by
  induction k with
  | zero =>
      show (baseInit input).toNat = _
      rw [WordFast.hornerAfter]
      unfold baseInit
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]
  | succ k ih =>
      show (hornerStep input k (hornerAfter input k)).toNat = _
      have hp : basePtr input k = 96 + (leadWidth input + 32 * k) := by
        show 96 + leadWidth input + 32 * k = _
        omega
      rw [WordFast.hornerAfter, ← ih]
      unfold hornerStep
      rw [addMod_toNat _ _ _ hmodpos hmodlt,
        mulMod_toNat _ _ _ hmodpos hmodlt, readWord_calldata, hp]

theorem wordBase_toNat (input : ByteArray) (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    (wordBase input).toNat =
      Precompile.bytesToNatPadded input 96 (baseSize input) % modulusValue input := by
  rw [wordBase, hornerAfter_toNat input hmodpos hmodlt]
  exact WordFast.baseLoop_correct input 96 (modulusValue input)
    (radixWord input).toNat (baseSize input)
    (by rw [radixWord_toNat input hmodpos hmodlt]; simp)

/-! ## The window table -/

theorem powTab_toNat (input : ByteArray) (base : UInt256)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbase : base.toNat < modulusValue input) :
    ∀ k, (powTab input base k).toNat =
      base.toNat ^ k % modulusValue input := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      match k with
      | 0 =>
          show ((1 : UInt256) % UInt256.ofNat (modulusValue input)).toNat = _
          change (UInt256.mod (1 : UInt256)
            (UInt256.ofNat (modulusValue input))).toNat = _
          unfold UInt256.mod
          rw [if_neg (modWord_ne _ hmodpos hmodlt)]
          change ((1 : UInt256).val % (UInt256.ofNat (modulusValue input)).val).val = _
          rw [Fin.val_mod]
          change (1 : UInt256).toNat % (UInt256.ofNat (modulusValue input)).toNat = _
          rw [show (1 : UInt256).toNat = 1 from by decide,
            Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt,
            pow_zero]
      | 1 =>
          show base.toNat = _
          rw [pow_one, Nat.mod_eq_of_lt hbase]
      | (n + 2) =>
          show (UInt256.mulMod base (powTab input base (n + 1))
            (UInt256.ofNat (modulusValue input))).toNat = _
          rw [mulMod_toNat _ _ _ hmodpos hmodlt, ih (n + 1) (by omega),
            right_mod_mul]
          congr 1
          rw [pow_succ]
          ring

/-! ## One exponent byte -/

theorem sqStep_toNat (input : ByteArray) (x : UInt256)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    (sqStep input x).toNat = x.toNat ^ 2 % modulusValue input := by
  unfold sqStep
  rw [mulMod_toNat _ _ _ hmodpos hmodlt, pow_two]

theorem sq4_toNat (input : ByteArray) (x : UInt256)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    (sq4 input x).toNat = x.toNat ^ 16 % modulusValue input := by
  have step : ∀ y : UInt256, (sqStep input y).toNat =
      y.toNat ^ 2 % modulusValue input := fun y =>
    sqStep_toNat input y hmodpos hmodlt
  have pow4 : ∀ a : Nat, ((((a ^ 2 % modulusValue input) ^ 2 %
      modulusValue input) ^ 2 % modulusValue input) ^ 2 %
        modulusValue input) = a ^ 16 % modulusValue input := by
    intro a
    have e1 : (a ^ 2 % modulusValue input) ^ 2 % modulusValue input
        = a ^ 4 % modulusValue input := by
      rw [← Nat.pow_mod]; congr 1; ring
    have e2 : (a ^ 4 % modulusValue input) ^ 2 % modulusValue input
        = a ^ 8 % modulusValue input := by
      rw [← Nat.pow_mod]; congr 1; ring
    have e3 : (a ^ 8 % modulusValue input) ^ 2 % modulusValue input
        = a ^ 16 % modulusValue input := by
      rw [← Nat.pow_mod]; congr 1; ring
    rw [e1, e2, e3]
  unfold sq4
  rw [step, step, step, step, pow4]

theorem windowStep_toNat (input : ByteArray) (base w acc : UInt256)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbase : base.toNat < modulusValue input)
    (hacc : acc.toNat < modulusValue input) :
    (windowStep input base w acc).toNat =
      (acc.toNat ^ 256 * base.toNat ^ w.toNat) % modulusValue input := by
  have hsq : ∀ x : Nat, x < modulusValue input →
      WordFast.sq (modulusValue input) 4 x = x ^ 16 % modulusValue input := by
    intro x hx
    simpa using WordFast.sq_spec (modulusValue input) 4 x hx
  have hspec := WordFast.windowByte_spec (modulusValue input) base.toNat
    acc.toNat w.toNat hmodpos hacc
  rw [← hspec]
  unfold WordFast.windowByte
  rw [hsq acc.toNat hacc, hsq _ (Nat.mod_lt _ hmodpos)]
  unfold windowStep tabHi tabLo
  rw [mulMod_toNat _ _ _ hmodpos hmodlt, sq4_toNat _ _ hmodpos hmodlt,
    mulMod_toNat _ _ _ hmodpos hmodlt, sq4_toNat _ _ hmodpos hmodlt,
    powTab_toNat input base hmodpos hmodlt hbase,
    powTab_toNat input base hmodpos hmodlt hbase]

/-! ## The exponent loop -/

theorem byteWord_toNat (input : ByteArray) (off : Nat) (hoff : off < 2 ^ 256) :
    (byteWord input off).toNat = Precompile.bytesToNatPadded input off 1 := by
  have h : byteWord input off =
      UInt256.byteAt ⟨0⟩ (MachineState.readWord input (UInt256.ofNat off).toNat) :=
    rfl
  rw [h, Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff,
    Challenge.EvmProof.Bytes.byteAt_zero_readWord,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt
      ((YulSemantics.EVM.byteFrom input.toList off).toNat_lt.trans (by norm_num))]
  have hone := Challenge.EvmProof.Bytes.bytesToNatPadded_succ input off 0
  rw [Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width] at hone
  simpa using hone.symm

theorem wordAcc_toNat (input : ByteArray) (base : UInt256)
    (hvalid : ValidInput input)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256)
    (hbase : base.toNat < modulusValue input) :
    ∀ i, i ≤ exponentSize input →
      (wordAcc input base i).toNat =
        WordFast.expAfter input (expOffset input) (modulusValue input) base.toNat
          i (1 % modulusValue input) := by
  obtain ⟨_, hb, he, _⟩ := hvalid
  have hexpv : expOffset input = 96 + baseSize input := rfl
  intro i
  induction i with
  | zero =>
      intro _
      show (powTab input base 0).toNat = _
      rw [powTab_toNat input base hmodpos hmodlt hbase, WordFast.expAfter,
        pow_zero]
  | succ i ih =>
      intro hle
      show (windowStep input base (byteWord input (expOffset input + i))
        (wordAcc input base i)).toNat = _
      have hih := ih (by omega)
      have haccLt : (wordAcc input base i).toNat < modulusValue input := by
        rw [hih]
        exact expAfter_lt input (expOffset input) (modulusValue input)
          base.toNat i (1 % modulusValue input) hmodpos
          (Nat.mod_lt _ hmodpos)
      rw [windowStep_toNat input base _ _ hmodpos hmodlt hbase haccLt, hih,
        WordFast.expAfter, WordFast.expStep,
        byteWord_toNat input (expOffset input + i) (by omega)]

/-- **The word path computes the precompile.**  `WordFast.wordPath_modPow`
carries the `m = 1` case, which is the one `T[0] = mod(1, m)` exists for. -/
theorem wordResult_toNat (input : ByteArray) (hvalid : ValidInput input)
    (hmodpos : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    (wordResult input).toNat =
      Precompile.modPow
        (Precompile.bytesToNatPadded input 96 (baseSize input))
        (Precompile.bytesToNatPadded input (expOffset input) (exponentSize input))
        (modulusValue input) := by
  have hbase : (wordBase input).toNat < modulusValue input := by
    rw [wordBase_toNat input hmodpos hmodlt]
    exact Nat.mod_lt _ hmodpos
  rw [wordResult,
    wordAcc_toNat input (wordBase input) hvalid hmodpos hmodlt hbase
      (exponentSize input) (le_refl _),
    WordFast.expAfter_spec input (expOffset input) (modulusValue input)
      (wordBase input).toNat (exponentSize input) (1 % modulusValue input)
      (Nat.mod_lt _ hmodpos),
    wordBase_toNat input hmodpos hmodlt]
  exact WordFast.wordPath_modPow
    (Precompile.bytesToNatPadded input 96 (baseSize input))
    (Precompile.bytesToNatPadded input (expOffset input) (exponentSize input))
    (modulusValue input) (exponentSize input) hmodpos

end Challenge.Modexp.Submission.Proofs.Bytecode.WordCorrect
