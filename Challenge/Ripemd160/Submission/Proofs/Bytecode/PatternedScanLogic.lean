import Batteries.Data.ByteArray
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedInputData

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData

def calldataByte (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord input i)

def expectedWord (i : Nat) : UInt256 :=
  UInt256.ofNat (expectedByte i).toNat

def scanAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | n + 1 =>
      UInt256.lor
        (UInt256.xor (expectedWord n) (calldataByte input n))
        (scanAcc input n)

theorem add_comm_word (a b : UInt256) : a + b = b + a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val + b.val).val = (b.val + a.val).val
  rw [Fin.val_add, Fin.val_add, Nat.add_comm]

theorem mul_comm_word (a b : UInt256) : a * b = b * a := by
  apply Challenge.EvmProof.Word.word_ext
  change (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

private theorem ofNat_mul (a b : Nat)
    (ha : a < 2 ^ 256) (hb : b < 2 ^ 256) (h : a * b < 2 ^ 256) :
    UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b) = UInt256.ofNat (a * b) := by
  apply Challenge.EvmProof.Word.word_ext
  have hmul : (UInt256.mul (UInt256.ofNat a) (UInt256.ofNat b)).toNat =
      ((UInt256.ofNat a).toNat * (UInt256.ofNat b).toNat) % 2 ^ 256 := by
    change ((UInt256.ofNat a).val * (UInt256.ofNat b).val).val = _
    rw [Fin.val_mul]
    rfl
  rw [hmul, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt ha, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hb, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt h]

private theorem ofNat_land_ff (n : Nat) (hn : n < 2 ^ 256) :
    UInt256.land (UInt256.ofNat n) (UInt256.ofNat 255) =
      UInt256.ofNat (n % 256) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by norm_num : 255 < 2 ^ 256)]
  have hmod : n % 256 < 2 ^ 256 :=
    Nat.lt_trans (Nat.mod_lt n (by decide)) (by norm_num)
  rw [Nat.mod_eq_of_lt hmod]
  change n &&& 255 = n % 256
  rw [show 255 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem expectedByte_toNat (i : Nat) :
    (expectedByte i).toNat = (i * 37 + i / 251 * 11 + 7) % 256 := by
  simp [expectedByte]

theorem expected_evm (n : Nat) (hn : n < 1000) :
    UInt256.land
      (UInt256.ofNat n * UInt256.ofNat 37 +
        UInt256.ofNat n / UInt256.ofNat 251 * UInt256.ofNat 11 +
        UInt256.ofNat 7)
      (UInt256.ofNat 255) = expectedWord n := by
  have hmul37 : n * 37 < 2 ^ 256 := by omega
  have hmul11 : (n / 251) * 11 < 2 ^ 256 := by omega
  have hmul : UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 37) =
      UInt256.ofNat (n * 37) := ofNat_mul n 37 (by omega) (by norm_num) hmul37
  have hmulq : UInt256.mul (UInt256.ofNat (n / 251)) (UInt256.ofNat 11) =
      UInt256.ofNat ((n / 251) * 11) :=
    ofNat_mul (n / 251) 11 (by omega) (by norm_num) hmul11
  have hdivv : UInt256.ofNat n / UInt256.ofNat 251 = UInt256.ofNat (n / 251) := by
    apply Challenge.EvmProof.Word.word_ext
    have hb : (UInt256.ofNat 251).toNat = 251 := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat]; decide
    have ha : (UInt256.ofNat n).toNat = n := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    change ((UInt256.ofNat n).val / (UInt256.ofNat 251).val).val = _
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    have hmod : n / 251 < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt hmod]
    change (UInt256.ofNat n).toNat / (UInt256.ofNat 251).toNat = n / 251
    rw [ha, hb]
  have hstar : UInt256.ofNat n * UInt256.ofNat 37 =
      UInt256.mul (UInt256.ofNat n) (UInt256.ofNat 37) := rfl
  have hstarq : UInt256.ofNat (n / 251) * UInt256.ofNat 11 =
      UInt256.mul (UInt256.ofNat (n / 251)) (UInt256.ofNat 11) := rfl
  rw [hstar, hmul, hdivv, hstarq, hmulq]
  have hadd₁ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := n * 37) (b := (n / 251) * 11) (by omega)
  have hadd₂ := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := n * 37 + (n / 251) * 11) (b := 7) (by omega)
  rw [hadd₁, hadd₂, ofNat_land_ff _ (by omega), expectedWord,
    expectedByte_toNat]

theorem calldataByte_eq (input : ByteArray) (i : Nat) (hi : i < input.size) :
    calldataByte input i = UInt256.ofNat input[i].toNat := by
  have hbyte := Challenge.EvmProof.Bytes.byteAt_zero_readWord input i
  have hfrom := Challenge.EvmProof.Bytes.memMatch_toList input i
  rw [dif_pos hi] at hfrom
  simpa [calldataByte, hfrom] using hbyte

theorem calldataByte_patterned (i : Nat) (hi : i < 1000) :
    calldataByte patternedInput i = expectedWord i := by
  have hsize : i < patternedInput.size := by
    rw [patternedInput_size]; exact hi
  rw [calldataByte_eq patternedInput i hsize, patternedInput_getElem i hsize,
    expectedWord]

theorem scanAcc_zero_iff (input : ByteArray) (n : Nat)
    (hbound : ∀ i, i < n → i < input.size) :
    scanAcc input n = 0 ↔
      ∀ (i : Nat) (hi : i < n), input[i]'(hbound i hi) = expectedByte i := by
  induction n with
  | zero => simp [scanAcc]
  | succ n ih =>
      rw [scanAcc, KnownInputLogic.wordOr_eq_zero_iff,
        KnownInputLogic.wordXor_eq_zero_iff,
        ih (fun i hi => hbound i (by omega))]
      constructor
      · rintro ⟨hcur, hprev⟩ i hi
        by_cases heq : i = n
        · subst i
          have hsz : n < input.size := hbound n (by omega)
          have hbyte := calldataByte_eq input n hsz
          rw [expectedWord, hbyte] at hcur
          apply UInt8.toNat_inj.mp
          have hn : (expectedByte n).toNat =
              (UInt256.ofNat (expectedByte n).toNat).toNat := by
            rw [Challenge.EvmProof.Word.word_toNat_ofNat]
            exact (Nat.mod_eq_of_lt
              (Nat.lt_trans (expectedByte n).toNat_lt (by norm_num))).symm
          have hg : input[n].toNat = (UInt256.ofNat input[n].toNat).toNat := by
            rw [Challenge.EvmProof.Word.word_toNat_ofNat]
            exact (Nat.mod_eq_of_lt
              (Nat.lt_trans input[n].toNat_lt (by norm_num))).symm
          rw [hn, hg, hcur]
        · exact hprev i (by omega)
      · intro hall
        refine ⟨?_, fun i hi => hall i (by omega)⟩
        have hsz : n < input.size := hbound n (by omega)
        rw [expectedWord, calldataByte_eq input n hsz, hall n (by omega)]

theorem scanAcc_patterned (n : Nat) (hn : n ≤ 1000) :
    scanAcc patternedInput n = 0 := by
  rw [scanAcc_zero_iff patternedInput n (fun i hi => by
    rw [patternedInput_size]; omega)]
  intro i hi
  exact patternedInput_getElem i (by rw [patternedInput_size]; omega)

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 1000) :
    scanAcc input 1000 = 0 ↔ input = patternedInput := by
  rw [scanAcc_zero_iff input 1000 (fun i hi => by rw [hsize]; exact hi)]
  constructor
  · intro hall
    apply ByteArray.ext_getElem
    · exact hsize.trans patternedInput_size.symm
    · intro i hi hiPattern
      have hi1000 : i < 1000 := by simpa [hsize] using hi
      exact (hall i hi1000).trans (patternedInput_getElem i hiPattern).symm
  · rintro rfl i hi
    exact patternedInput_getElem i (by rw [patternedInput_size]; exact hi)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic
