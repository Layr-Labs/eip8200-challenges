import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Limbs
import Challenge.Modexp.Submission.Proofs.Montgomery.WordArithmetic
import Challenge.Modexp.Submission.Proofs.Montgomery.HighArithmetic
import Mathlib.Tactic

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory

open EvmSemantics

def B : Nat := 2 ^ 256

private theorem B_pos : 0 < B := by
  norm_num [B]

private theorem B_gt_two : 2 < B := by
  norm_num [B]

private theorem word_toNat_mul (x y : UInt256) :
    (x * y).toNat = (x.toNat * y.toNat) % B := by
  change (x.val * y.val).val = _
  rw [Fin.val_mul]
  rfl

def wordStep (memory : ByteArray) (x t j : Nat) (word carry : UInt256) :
    ByteArray × UInt256 :=
  let xv := MachineState.readWord memory (x + 32 * j)
  let old := MachineState.readWord memory (t + 32 * j)
  let lo := xv * word
  let hi := HighArithmetic.fullHighWord xv word
  let s := old + lo
  let z := s + carry
  let flags := UInt256.lt s old + UInt256.lt z s
  (MachineState.writeBytes memory
      (Data.Bytes.natToBytesPadded z.toNat 32) (t + 32 * j), hi + flags)

private theorem wordStep_arithmetic (xv old word carry : UInt256)
    (hcarry : carry.toNat ≤ word.toNat) :
    let lo := xv * word
    let hi := HighArithmetic.fullHighWord xv word
    let s := old + lo
    let z := s + carry
    let flags := UInt256.lt s old + UInt256.lt z s
    let total := xv.toNat * word.toNat + old.toNat + carry.toNat
    z.toNat = total % B ∧
      (hi + flags).toNat = total / B ∧
      (hi + flags).toNat ≤ word.toNat := by
  dsimp only
  have hxv : xv.toNat < B := by
    change xv.val.val < 2 ^ 256
    exact xv.val.isLt
  have hold : old.toNat < B := by
    change old.val.val < 2 ^ 256
    exact old.val.isLt
  have hword : word.toNat < B := by
    change word.val.val < 2 ^ 256
    exact word.val.isLt
  have hcarryB : carry.toNat < B := lt_of_le_of_lt hcarry hword
  have hlow : (xv * word).toNat =
      (xv.toNat * word.toNat) % B := word_toNat_mul xv word
  have hhi : (HighArithmetic.fullHighWord xv word).toNat =
      (xv.toNat * word.toNat) / B := by
    simpa [B, HighArithmetic.B] using
      (HighArithmetic.fullHighWord_toNat xv word)
  have hlowLt : (xv * word).toNat < B := by
    change (xv * word).val.val < 2 ^ 256
    exact (xv * word).val.isLt
  have hthree :=
    WordArithmetic.three_term_carry old.toNat (xv * word).toNat
      carry.toNat hold hlowLt hcarryB
  have hs : (old + xv * word).toNat =
      (old.toNat + (xv * word).toNat) % B := by
    simpa [B] using
      (Challenge.EvmProof.Word.word_toNat_add old (xv * word))
  have hz : ((old + xv * word) + carry).toNat =
      ((old + xv * word).toNat + carry.toNat) % B := by
    simpa [B] using
      (Challenge.EvmProof.Word.word_toNat_add (old + xv * word) carry)
  have hlt1 :
      (UInt256.lt (old + xv * word) old).toNat =
        if (old + xv * word).toNat < old.toNat then 1 else 0 :=
    Challenge.EvmProof.Word.word_toNat_lt (old + xv * word) old
  have hlt2 :
      (UInt256.lt ((old + xv * word) + carry) (old + xv * word)).toNat =
        if ((old + xv * word) + carry).toNat <
            (old + xv * word).toNat then 1 else 0 :=
    Challenge.EvmProof.Word.word_toNat_lt ((old + xv * word) + carry)
      (old + xv * word)
  have hflags :
      (UInt256.lt (old + xv * word) old +
        UInt256.lt ((old + xv * word) + carry) (old + xv * word)).toNat =
          (old.toNat + (xv * word).toNat + carry.toNat) / B := by
    have hsmall :
        (if (old + xv * word).toNat < old.toNat then 1 else 0) +
            (if ((old + xv * word) + carry).toNat <
                (old + xv * word).toNat then 1 else 0) < B := by
      split <;> split <;> norm_num [B]
    calc
      _ = ((if (old + xv * word).toNat < old.toNat then 1 else 0) +
          (if ((old + xv * word) + carry).toNat <
            (old + xv * word).toNat then 1 else 0)) % B := by
        simpa [B] using
          (Challenge.EvmProof.Word.word_toNat_add
            (UInt256.lt (old + xv * word) old)
            (UInt256.lt ((old + xv * word) + carry) (old + xv * word)))
          |>.trans (congrArg (fun q => q % B) (by rw [hlt1, hlt2]))
      _ = (if (old + xv * word).toNat < old.toNat then 1 else 0) +
          (if ((old + xv * word) + carry).toNat <
            (old + xv * word).toNat then 1 else 0) :=
        Nat.mod_eq_of_lt hsmall
      _ = (old.toNat + (xv * word).toNat + carry.toNat) / B := by
        have hflag1eq :
            (if (old.toNat + (xv * word).toNat) % B < old.toNat then 1 else 0) =
              (if (old + xv * word).toNat < old.toNat then 1 else 0) := by
          rw [hs]
        have hflag2eq :
            (if (((old.toNat + (xv * word).toNat) % B + carry.toNat) % B <
                (old.toNat + (xv * word).toNat) % B) then 1 else 0) =
              (if ((old + xv * word) + carry).toNat <
                (old + xv * word).toNat then 1 else 0) := by
          rw [hz, hs]
        rw [← hflag1eq, ← hflag2eq]
        change
          (if (old.toNat + (xv * word).toNat) %
              WordArithmetic.montRadix < old.toNat then 1 else 0) +
              (if (((old.toNat + (xv * word).toNat) %
                  WordArithmetic.montRadix + carry.toNat) %
                    WordArithmetic.montRadix <
                (old.toNat + (xv * word).toNat) %
                  WordArithmetic.montRadix) then 1 else 0) =
            (old.toNat + (xv * word).toNat + carry.toNat) /
              WordArithmetic.montRadix
        exact hthree.2
  have hlowSum : ((old + xv * word) + carry).toNat =
      (xv.toNat * word.toNat + old.toNat + carry.toNat) % B := by
    calc
      ((old + xv * word) + carry).toNat =
          ((old + xv * word).toNat + carry.toNat) % B := hz
      _ = ((old.toNat + (xv * word).toNat) % B + carry.toNat) % B := by
        rw [hs]
      _ = (old.toNat + (xv * word).toNat + carry.toNat) % B := hthree.1
      _ = (xv.toNat * word.toNat + old.toNat + carry.toNat) % B := by
        have hmod :=
          (Nat.mod_modEq (xv.toNat * word.toNat) B).add
            (Nat.ModEq.refl old.toNat)
        have hmod' := hmod.add (Nat.ModEq.refl carry.toNat)
        rw [Nat.ModEq] at hmod'
        simpa [hlow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmod'
  have hfull :
      (xv.toNat * word.toNat) % B +
          B * ((xv.toNat * word.toNat) / B) =
        xv.toNat * word.toNat := by
    simpa [B, WordArithmetic.montRadix, WordArithmetic.fullLo,
      WordArithmetic.fullHi] using
      (WordArithmetic.fullMul_value xv.toNat word.toNat)
  have hfull' :
      (xv * word).toNat + B * ((xv.toNat * word.toNat) / B) =
        xv.toNat * word.toNat := by
    rw [hlow]
    exact hfull
  have hstep :
      (xv.toNat * word.toNat) / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B ≤
        word.toNat := by
    have hstep' := WordArithmetic.step_carry_le
      xv.toNat old.toNat word.toNat carry.toNat hxv hold hword hcarry
    simpa [B, WordArithmetic.montRadix, WordArithmetic.fullLo,
      WordArithmetic.fullHi, hlow] using hstep'
  have hdiv :
      (xv.toNat * word.toNat + old.toNat + carry.toNat) / B =
        (xv.toNat * word.toNat) / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B := by
    have hsum := Nat.mod_add_div
      (old.toNat + (xv * word).toNat + carry.toNat) B
    have hsumLt :
        (old.toNat + (xv * word).toNat + carry.toNat) % B < B :=
      Nat.mod_lt _ B_pos
    have hsum' :
        old.toNat + (xv * word).toNat + carry.toNat =
          (old.toNat + (xv * word).toNat + carry.toNat) % B +
            B * ((old.toNat + (xv * word).toNat + carry.toNat) / B) :=
      hsum.symm
    have hdecomp :
        xv.toNat * word.toNat + old.toNat + carry.toNat =
          (old.toNat + (xv * word).toNat + carry.toNat) % B +
            B * ((xv.toNat * word.toNat) / B +
              (old.toNat + (xv * word).toNat + carry.toNat) / B) := by
      calc
        xv.toNat * word.toNat + old.toNat + carry.toNat =
            (xv * word).toNat +
              B * ((xv.toNat * word.toNat) / B) +
              old.toNat + carry.toNat := by rw [hfull']
        _ = old.toNat + (xv * word).toNat + carry.toNat +
              B * ((xv.toNat * word.toNat) / B) := by omega
        _ = (old.toNat + (xv * word).toNat + carry.toNat) % B +
              B * ((old.toNat + (xv * word).toNat + carry.toNat) / B) +
              B * ((xv.toNat * word.toNat) / B) := by
          simpa using (congrArg
            (fun q => q + B * ((xv.toNat * word.toNat) / B)) hsum'.symm).symm
        _ = (old.toNat + (xv * word).toNat + carry.toNat) % B +
              B * ((xv.toNat * word.toNat) / B +
                (old.toNat + (xv * word).toNat + carry.toNat) / B) := by
          ring
    rw [hdecomp, Nat.add_mul_div_left _ _ B_pos,
      Nat.div_eq_of_lt hsumLt, Nat.zero_add]
  have hstepLt :
      (xv.toNat * word.toNat) / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B < B :=
    lt_of_le_of_lt hstep hword
  constructor
  · exact hlowSum
  constructor
  · calc
      (HighArithmetic.fullHighWord xv word +
          (UInt256.lt (old + xv * word) old +
            UInt256.lt ((old + xv * word) + carry) (old + xv * word))).toNat =
          ((HighArithmetic.fullHighWord xv word).toNat +
            (UInt256.lt (old + xv * word) old +
              UInt256.lt ((old + xv * word) + carry) (old + xv * word)).toNat) % B := by
            simpa [B] using
              (Challenge.EvmProof.Word.word_toNat_add
                (HighArithmetic.fullHighWord xv word)
                (UInt256.lt (old + xv * word) old +
                  UInt256.lt ((old + xv * word) + carry) (old + xv * word)))
      _ = ((xv.toNat * word.toNat) / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B) % B := by
        rw [hhi, hflags]
      _ = xv.toNat * word.toNat / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B :=
        Nat.mod_eq_of_lt hstepLt
      _ = (xv.toNat * word.toNat + old.toNat + carry.toNat) / B :=
        hdiv.symm
  · calc
      (HighArithmetic.fullHighWord xv word +
          (UInt256.lt (old + xv * word) old +
            UInt256.lt ((old + xv * word) + carry) (old + xv * word))).toNat =
          ((HighArithmetic.fullHighWord xv word).toNat +
            (UInt256.lt (old + xv * word) old +
              UInt256.lt ((old + xv * word) + carry) (old + xv * word)).toNat) % B := by
            simpa [B] using
              (Challenge.EvmProof.Word.word_toNat_add
                (HighArithmetic.fullHighWord xv word)
                (UInt256.lt (old + xv * word) old +
                  UInt256.lt ((old + xv * word) + carry) (old + xv * word)))
      _ = ((xv.toNat * word.toNat) / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B) % B := by
        rw [hhi, hflags]
      _ = xv.toNat * word.toNat / B +
          (old.toNat + (xv * word).toNat + carry.toNat) / B :=
        Nat.mod_eq_of_lt hstepLt
      _ ≤ word.toNat := hstep

private theorem top_carry (h c : Nat) (hh : h < B) (hc : c < B) :
    (h + c) / B ≤ 1 ∧
      (if (h + c) % B < h then 1 else 0) = (h + c) / B := by
  have hsum : h + c < 2 * B := by omega
  constructor
  · rw [Nat.div_le_iff_le_mul B_pos]
    omega
  · by_cases hlt : h + c < B
    · rw [Nat.mod_eq_of_lt hlt, if_neg (by omega), Nat.div_eq_of_lt hlt]
    · have hle : B ≤ h + c := by omega
      have hmod : (h + c) % B = h + c - B := by
        rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt (by omega)]
      rw [hmod, if_pos (by omega)]
      exact (Nat.div_eq_of_lt_le
        (by omega : 1 * B ≤ h + c)
        (by omega : h + c < (1 + 1) * B)).symm

private theorem top_arithmetic (h c : UInt256) (hc : c.toNat < B) :
    let z := h + c
    let e := UInt256.lt z h
    let total := h.toNat + c.toNat
    z.toNat = total % B ∧
      total / B ≤ 1 ∧
      e.toNat = total / B := by
  dsimp only
  have hh : h.toNat < B := by
    change h.val.val < 2 ^ 256
    exact h.val.isLt
  have hz : (h + c).toNat = (h.toNat + c.toNat) % B := by
    simpa [B] using Challenge.EvmProof.Word.word_toNat_add h c
  have he : (UInt256.lt (h + c) h).toNat =
      if (h + c).toNat < h.toNat then 1 else 0 :=
    Challenge.EvmProof.Word.word_toNat_lt (h + c) h
  have htop := top_carry h.toNat c.toNat hh hc
  constructor
  · exact hz
  constructor
  · exact htop.1
  · calc
      (UInt256.lt (h + c) h).toNat =
          if (h + c).toNat < h.toNat then 1 else 0 := he
      _ = if (h.toNat + c.toNat) % B < h.toNat then 1 else 0 := by
        rw [hz]
      _ = (h.toNat + c.toNat) / B := htop.2

def foldTop (memory : ByteArray) (t n : Nat) (carry : UInt256) : ByteArray :=
  let topAt := t + 32 * n
  let nextAt := topAt + 32
  let h := MachineState.readWord memory topAt
  let k := MachineState.readWord memory nextAt
  let z := h + carry
  let e := UInt256.lt z h
  let afterTop := MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded z.toNat 32) topAt
  MachineState.writeBytes afterTop
    (Data.Bytes.natToBytesPadded (k + e).toNat 32) nextAt

theorem wordStep_correct (memory : ByteArray) (x t j : Nat)
    (word carry : UInt256)
    (hcarry : carry.toNat ≤ word.toNat)
    (_hxfit : x + 32 * j < B)
    (_htfit : t + 32 * j < B) :
    let xv := MachineState.readWord memory (x + 32 * j)
    let old := MachineState.readWord memory (t + 32 * j)
    let total := xv.toNat * word.toNat + old.toNat + carry.toNat
    let result := wordStep memory x t j word carry
    (MachineState.readWord result.1 (t + 32 * j)).toNat = total % B ∧
      result.2.toNat = total / B ∧
      result.2.toNat ≤ word.toNat ∧
      ∀ i, ¬ (t + 32 * j ≤ i ∧ i < t + 32 * j + 32) →
        result.1[i]?.getD 0 = memory[i]?.getD 0 := by
  dsimp only
  let addr := t + 32 * j
  let xv := MachineState.readWord memory (x + 32 * j)
  let old := MachineState.readWord memory addr
  let z := (old + xv * word) + carry
  let total := xv.toNat * word.toNat + old.toNat + carry.toNat
  let result := wordStep memory x t j word carry
  change
    (MachineState.readWord result.1 addr).toNat = total % B ∧
      result.2.toNat = total / B ∧
      result.2.toNat ≤ word.toNat ∧
      ∀ i, ¬ (addr ≤ i ∧ i < addr + 32) →
        result.1[i]?.getD 0 = memory[i]?.getD 0
  have harith := wordStep_arithmetic xv old word carry hcarry
  have hlow : z.toNat = total % B := by
    simpa [z, total] using harith.1
  have hnext :
      (HighArithmetic.fullHighWord xv word +
        (UInt256.lt (old + xv * word) old +
          UInt256.lt ((old + xv * word) + carry) (old + xv * word))).toNat =
        total / B := by
    simpa [total] using harith.2.1
  have hnextLe :
      (HighArithmetic.fullHighWord xv word +
        (UInt256.lt (old + xv * word) old +
          UInt256.lt ((old + xv * word) + carry) (old + xv * word))).toNat ≤
        word.toNat := by
    simpa using harith.2.2
  have hread :
      MachineState.readWord
          (MachineState.writeBytes memory
            (Data.Bytes.natToBytesPadded z.toNat 32) addr) addr = z := by
    exact Challenge.EvmProof.Memory.readWord_writeWord memory addr z
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hreadNat := congrArg UInt256.toNat hread
    simpa [result, wordStep, addr, xv, old, z] using hreadNat.trans hlow
  · simpa [result, wordStep, addr, xv, old, z] using hnext
  · simpa [result, wordStep, addr, xv, old, z] using hnextLe
  · intro i hi
    change
      (MachineState.writeBytes memory
        (Data.Bytes.natToBytesPadded z.toNat 32) addr)[i]?.getD 0 =
          memory[i]?.getD 0
    rw [MachineState.writeBytes_getElem?_getD]
    apply if_neg
    intro hwin
    apply hi
    have hsize :
        (Data.Bytes.natToBytesPadded z.toNat 32).size = 32 := by
      simp [Data.Bytes.natToBytesPadded, ByteArray.size]
    exact ⟨hwin.1, by simpa [hsize] using hwin.2⟩

theorem foldTop_correct (memory : ByteArray) (t n : Nat) (carry : UInt256)
    (hcarry : carry.toNat < B)
    (hnoWrap :
      (MachineState.readWord memory (t + 32 * n + 32)).toNat +
          (UInt256.lt
            (MachineState.readWord memory (t + 32 * n) + carry)
            (MachineState.readWord memory (t + 32 * n))).toNat < B) :
    let topAt := t + 32 * n
    let nextAt := topAt + 32
    let h := MachineState.readWord memory topAt
    let k := MachineState.readWord memory nextAt
    let total := h.toNat + carry.toNat
    let result := foldTop memory t n carry
    (MachineState.readWord result topAt).toNat = total % B ∧
      (MachineState.readWord result nextAt).toNat =
        k.toNat + total / B ∧
      total / B ≤ 1 ∧
      (UInt256.lt (h + carry) h).toNat = total / B ∧
      ∀ i, i < topAt ∨ topAt + 64 ≤ i →
        result[i]?.getD 0 = memory[i]?.getD 0 := by
  dsimp only
  let topAt := t + 32 * n
  let nextAt := topAt + 32
  let h := MachineState.readWord memory topAt
  let k := MachineState.readWord memory nextAt
  let z := h + carry
  let e := UInt256.lt z h
  let total := h.toNat + carry.toNat
  let topBytes := Data.Bytes.natToBytesPadded z.toNat 32
  let nextBytes := Data.Bytes.natToBytesPadded (k + e).toNat 32
  let first := MachineState.writeBytes memory topBytes topAt
  let result := MachineState.writeBytes first nextBytes nextAt
  change
    (MachineState.readWord result topAt).toNat = total % B ∧
      (MachineState.readWord result nextAt).toNat =
        k.toNat + total / B ∧
      total / B ≤ 1 ∧
      e.toNat = total / B ∧
      ∀ i, i < topAt ∨ topAt + 64 ≤ i →
        result[i]?.getD 0 = memory[i]?.getD 0
  have harith := top_arithmetic h carry hcarry
  have hz : z.toNat = total % B := by
    simpa [z, total] using harith.1
  have hqle : total / B ≤ 1 := by
    simpa [total] using harith.2.1
  have he : e.toNat = total / B := by
    simpa [z, e, total] using harith.2.2
  have hnow : k.toNat + e.toNat < B := by
    change
      (MachineState.readWord memory (t + 32 * n + 32)).toNat +
          (UInt256.lt
            (MachineState.readWord memory (t + 32 * n) + carry)
            (MachineState.readWord memory (t + 32 * n))).toNat < B
    exact hnoWrap
  have htopBytes : topBytes.size = 32 := by
    simp [topBytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  have hnextBytes : nextBytes.size = 32 := by
    simp [nextBytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  have htopRead :
      MachineState.readWord (MachineState.writeBytes memory topBytes topAt)
          topAt = z := by
    simpa [topBytes] using
      (Challenge.EvmProof.Memory.readWord_writeWord memory topAt z)
  have htopUnchanged :
      MachineState.readWord result topAt =
        MachineState.readWord (MachineState.writeBytes memory topBytes topAt)
          topAt := by
    apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
    left
    dsimp only [nextAt]
    omega
  have hnextRead : MachineState.readWord result nextAt = k + e := by
    simpa [nextBytes] using
      (Challenge.EvmProof.Memory.readWord_writeWord
        (MachineState.writeBytes memory topBytes topAt) nextAt (k + e))
  have hnextNat : (k + e).toNat = k.toNat + e.toNat := by
    calc
      (k + e).toNat = (k.toNat + e.toNat) % B := by
        simpa [B] using Challenge.EvmProof.Word.word_toNat_add k e
      _ = k.toNat + e.toNat := Nat.mod_eq_of_lt hnow
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hreadNat := congrArg UInt256.toNat htopRead
    calc
      (MachineState.readWord result topAt).toNat =
          (MachineState.readWord
            (MachineState.writeBytes memory topBytes topAt) topAt).toNat := by
            exact congrArg UInt256.toNat htopUnchanged
      _ = z.toNat := hreadNat
      _ = total % B := hz
  · have hreadNat := congrArg UInt256.toNat hnextRead
    calc
      (MachineState.readWord result nextAt).toNat = (k + e).toNat := hreadNat
      _ = k.toNat + e.toNat := hnextNat
      _ = k.toNat + total / B := by rw [he]
  · exact hqle
  · exact he
  · intro i hi
    rw [MachineState.writeBytes_getElem?_getD]
    have hnotNext : ¬ (nextAt ≤ i ∧ i < nextAt + nextBytes.size) := by
      intro hwin
      rcases hi with hbefore | hafter
      · have hnextLower : topAt + 32 ≤ nextAt := by
          dsimp only [nextAt]
          omega
        omega
      · rw [hnextBytes] at hwin
        dsimp only [nextAt] at hwin
        omega
    rw [if_neg hnotNext]
    rw [MachineState.writeBytes_getElem?_getD]
    apply if_neg
    intro hwin
    rcases hi with hbefore | hafter
    · omega
    · rw [htopBytes] at hwin
      omega

end Challenge.Modexp.Submission.Proofs.Montgomery.WordMemory
