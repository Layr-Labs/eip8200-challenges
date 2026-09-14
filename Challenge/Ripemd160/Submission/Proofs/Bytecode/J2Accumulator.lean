import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAccumulator

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RecognitionAccumulator PatternedInputData TailProjection

def offset (k : Nat) : Nat := 251 * (k / 8) + 32 * (k % 8)
def width (n k : Nat) : Nat := min 32 (min (n - offset k) (251 - 32 * (k % 8)))
def shift (n k : Nat) : UInt256 := UInt256.ofNat ((32 - width n k) * 8)

def wordAt : Nat → UInt256
  | 0 => PatternedSwar.P
  | k + 1 => RecognitionRecurrence.advance (if k % 8 = 7 then 114 else 32) (wordAt k)

def piece (input : ByteArray) (n k : Nat) : UInt256 :=
  UInt256.shiftRight (UInt256.xor (MachineState.readWord input (offset k)) (wordAt k)) (shift n k)

def accumulate (input : ByteArray) (n : Nat) : Nat → UInt256
  | 0 => 0
  | k + 1 => UInt256.lor (piece input n k) (accumulate input n k)

def resultAcc (input : ByteArray) (n : Nat) : UInt256 := accumulate input n 32

theorem accumulate_zero_iff (input : ByteArray) (n count : Nat) :
    accumulate input n count = 0 ↔ ∀ k, k < count → piece input n k = 0 := by
  induction count with
  | zero => simp [accumulate]
  | succ count ih =>
    rw [accumulate, KnownInputLogic.wordOr_eq_zero_iff, ih]
    constructor
    · rintro ⟨hlast, hprev⟩ k hk
      by_cases he : k = count
      · subst k; exact hlast
      · exact hprev k (by omega)
    · intro h
      exact ⟨h count (by omega), fun k hk => h k (by omega)⟩

private def knownWord (k : Nat) : UInt256 := UInt256.ofNat
  ((List.range 32).foldl (fun acc j => acc * 256 +
    (PatternedWordData.paddedByte (offset k + j)).toNat) 0)

private theorem readWord_known (k : Nat) :
    MachineState.readWord patternedInput (offset k) = knownWord k := by
  have hb := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow patternedInput (offset k) 32
  rw [PatternedWordLogic.bytesToNatPadded_eq] at hb
  have hp : (256 : Nat)^32 = 2^256 := by norm_num
  rw [hp] at hb
  apply Word.word_ext
  rw [Challenge.EvmProof.Bytes.readWord_toNat, knownWord, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hb, PatternedWordLogic.bytesToNatPadded_eq]

private theorem full_projection_closed : ∀ k : Fin 32,
    UInt256.shiftRight (wordAt k.val) (shift 1000 k.val) =
      UInt256.shiftRight (knownWord k.val) (shift 1000 k.val) := by
  decide

private theorem full_projection (k : Fin 32) :
    UInt256.shiftRight (wordAt k.val) (shift 1000 k.val) =
      UInt256.shiftRight (MachineState.readWord patternedInput (offset k.val)) (shift 1000 k.val) := by
  rw [readWord_known]
  exact full_projection_closed k

private theorem full_width_pos : ∀ k : Fin 32, 0 < width 1000 k.val := by decide

private theorem shr256 (x : UInt256) : UInt256.shiftRight x (UInt256.ofNat 256) = 0 := by
  rfl

private theorem shrink (a b : UInt256) (p q : Nat) (hp : p < 256) (hq : q < 256)
    (hpq : p ≤ q)
    (h : UInt256.shiftRight a (UInt256.ofNat p) = UInt256.shiftRight b (UInt256.ofNat p)) :
    UInt256.shiftRight a (UInt256.ofNat q) = UInt256.shiftRight b (UInt256.ofNat q) := by
  apply Word.word_ext
  have he := congrArg UInt256.toNat h
  rw [Word.shiftRight_toNat a hp, Word.shiftRight_toNat b hp] at he
  rw [Word.shiftRight_toNat a hq, Word.shiftRight_toNat b hq]
  have hh := congrArg (fun x : Nat => x >>> (q - p)) he
  simpa only [← Nat.shiftRight_add, Nat.add_sub_of_le hpq] using hh

theorem projection (n k : Nat) (hn : n ≤ 1000) (hk : k < 32) :
    UInt256.shiftRight (wordAt k) (shift n k) =
      UInt256.shiftRight (MachineState.readWord (reference n) (offset k)) (shift n k) := by
  have hw : width n k ≤ 32 := Nat.min_le_left _ _
  by_cases hz : width n k = 0
  · simp only [shift, hz, Nat.sub_zero, Nat.reduceMul, shr256]
  have hp : 0 < width n k := by omega
  have hb : width n k ≤ width 1000 k := by unfold width; omega
  have hfull := full_width_pos ⟨k,hk⟩
  have hfull32 : width 1000 k ≤ 32 := Nat.min_le_left _ _
  have hfit : offset k + width n k ≤ n := by unfold width at hp ⊢; omega
  have he := shrink (wordAt k) (MachineState.readWord patternedInput (offset k))
    ((32 - width 1000 k)*8) ((32-width n k)*8) (by omega) (by omega) (by omega)
    (full_projection ⟨k,hk⟩)
  change UInt256.shiftRight (wordAt k) (UInt256.ofNat ((32-width n k)*8)) = _
  rw [he]
  unfold shift
  rw [Challenge.EvmProof.Bytes.shiftRight_readWord patternedInput (offset k) (width n k) hp hw,
    Challenge.EvmProof.Bytes.shiftRight_readWord (reference n) (offset k) (width n k) hp hw,
    bytesToNatPadded_reference n (offset k) (width n k) hn hfit]

theorem coverage (n i : Nat) (hn : n ≤ 1000) (hi : i < n) :
    ∃ k, k < 32 ∧ offset k ≤ i ∧ i - offset k < width n k := by
  let k := 8 * (i / 251) + (i % 251) / 32
  have hb : i / 251 < 4 := by omega
  have hj : (i % 251) / 32 < 8 := by omega
  have hdiv : k / 8 = i / 251 := by dsimp [k]; omega
  have hmod : k % 8 = (i % 251) / 32 := by dsimp [k]; omega
  have ho : offset k = 251 * (i / 251) + 32 * ((i % 251) / 32) := by
    simp only [offset, hdiv, hmod]
  refine ⟨k, by dsimp [k]; omega, ?_, ?_⟩
  · rw [ho]; omega
  · simp only [width, ho, hmod]; omega

theorem resultAcc_zero_iff (input : ByteArray) (n : Nat) (hn : Allowed n)
    (hsize : input.size = n) : resultAcc input n = 0 ↔ input = reference n := by
  have hn1000 := (allowed_bounds n hn).2
  have hs : input.size = (reference n).size := by rw [reference_size n hn1000]; exact hsize
  rw [resultAcc, accumulate_zero_iff]
  constructor
  · intro h
    apply ByteArray.ext_getElem hs
    intro i hi hir
    obtain ⟨k,hk,hstart,hrem⟩ := coverage n i hn1000 (by omega)
    have hp : 0 < width n k := by omega
    have hw : width n k ≤ 32 := Nat.min_le_left _ _
    have he := (shifted_xor_zero_iff _ _ _).mp (h k hk)
    change UInt256.shiftRight (MachineState.readWord input (offset k)) (shift n k) =
      UInt256.shiftRight (wordAt k) (shift n k) at he
    rw [projection n k hn1000 hk] at he
    have hzero := (shifted_xor_zero_iff _ _ _).mpr he
    have hb := (shifted_readWord_xor_zero_iff_bytes input (reference n) (offset k)
      (width n k) hp hw).mp hzero (i-offset k) hrem
    have hadd : offset k + (i-offset k) = i := by omega
    rw [hadd, byteFrom_getElem input i hi, byteFrom_getElem (reference n) i hir] at hb
    exact hb
  · rintro rfl k hk
    apply (shifted_xor_zero_iff _ _ _).mpr
    exact (projection n k hn1000 hk).symm

theorem modulus_constructor :
    UInt256.shiftLeft (UInt256.ofNat 2) (UInt256.ofNat 144) =
      UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 145) := by decide

#print axioms resultAcc_zero_iff
#print axioms modulus_constructor
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Accumulator
