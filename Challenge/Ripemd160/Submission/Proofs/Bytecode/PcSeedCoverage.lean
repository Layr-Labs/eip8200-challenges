import Challenge.Ripemd160.Submission.Proofs.Bytecode.Low64Anchor
import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! Candidate research only: universal coverage lemma for the PC48 scanner.
This file does not replace the certified submission or claim an artifact binding.
- basic equality comparisons at starts16+32*k (k<30), plus968 and0;
- the existing low64 anchor;
- all1000bytes covered with eight anchored equality classes.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedCoverage
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def byte (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.ofNat (YulSemantics.EVM.byteFrom input.toList i).toNat

theorem byte_eq_of_word (input : ByteArray) (a b i : Nat) (hi : i < 32)
    (h : MachineState.readWord input a = MachineState.readWord input b) :
    byte input (a+i) = byte input (b+i) := by
  have hh := congrArg (UInt256.byteAt (UInt256.ofNat i)) h
  simpa only [Bytes.byteAt_readWord input a i hi,
    Bytes.byteAt_readWord input b i hi, byte] using hh

theorem anchor_byte (r : UInt256)
    (hmod : r.toNat % Low64Anchor.B = Low64Anchor.low64)
    (i : Nat) (hi : 24 ≤ i ∧ i < 32) :
    UInt256.byteAt (UInt256.ofNat i) r = UInt256.ofNat 97 := by
  rcases hi with ⟨hlo, hhi⟩
  interval_cases i <;>
    apply Word.word_ext <;>
    norm_num [UInt256.byteAt, Word.word_toNat_ofNat, Nat.shiftRight_eq_div_pow] <;>
    rw [show 255 = 2^8-1 by decide, Nat.and_two_pow_sub_one_eq_mod] <;>
    norm_num [Low64Anchor.B, Low64Anchor.low64] at hmod ⊢ <;> omega

theorem reference_bytes (input : ByteArray)
    (h16 : MachineState.readWord input 16 = MachineState.readWord input 0)
    (h944 : MachineState.readWord input 944 = MachineState.readWord input 0)
    (h968 : MachineState.readWord input 968 = MachineState.readWord input 0)
    (hmod : (MachineState.readWord input 0).toNat % Low64Anchor.B = Low64Anchor.low64) :
    ∀ i, i < 32 → byte input i = UInt256.ofNat 97 := by
  have ha (i : Nat) (hi : 24 ≤ i ∧ i < 32) : byte input i = UInt256.ofNat 97 := by
    have h := anchor_byte (MachineState.readWord input 0) hmod i hi
    simpa only [Bytes.byteAt_readWord input 0 i hi.2, Nat.zero_add, byte] using h
  have hshift16 (i : Nat) (hi : i < 16) : byte input (i+16) = byte input i := by
    simpa only [Nat.zero_add, Nat.add_comm, Nat.add_zero] using
      byte_eq_of_word input 16 0 i (by omega) h16
  have hshift24 (i : Nat) (hi : i < 8) : byte input i = byte input (i+24) := by
    have h1 := byte_eq_of_word input 944 0 (24+i) (by omega) h944
    have h2 := byte_eq_of_word input 968 0 i (by omega) h968
    have he : 944+(24+i) = 968+i := by omega
    rw [he, Nat.zero_add] at h1
    rw [Nat.zero_add] at h2
    simpa only [Nat.add_comm] using h2.symm.trans h1
  have hfirst (i : Nat) (hi : i < 16) : byte input i = UInt256.ofNat 97 := by
    by_cases he : i < 8
    · exact (hshift24 i he).trans (ha (i+24) (by omega))
    · exact (hshift16 i hi).symm.trans (ha (i+16) (by omega))
  intro i hi
  by_cases he : i < 16
  · exact hfirst i he
  · by_cases he2 : i < 24
    · have hh := hshift16 (i-16) (by omega)
      rw [Nat.sub_add_cancel (by omega : 16 ≤ i)] at hh
      exact hh.trans (hfirst (i-16) (by omega))
    · exact ha i (by omega)

/-- Every byte is constrained, including the final eight bytes.  This is
universal in input, not a finite validation-vector claim. -/
theorem all_bytes (input : ByteArray)
    (hmain : ∀ k, k < 30 → MachineState.readWord input (16+32*k) = MachineState.readWord input 0)
    (h968 : MachineState.readWord input 968 = MachineState.readWord input 0)
    (hmod : (MachineState.readWord input 0).toNat % Low64Anchor.B = Low64Anchor.low64) :
    ∀ j, j < 1000 → byte input j = UInt256.ofNat 97 := by
  have href := reference_bytes input (hmain 0 (by decide)) (hmain 29 (by decide)) h968 hmod
  intro j hj
  by_cases hsmall : j < 16
  · exact href j (by omega)
  · by_cases hlast : 968 ≤ j
    · have he := byte_eq_of_word input 968 0 (j-968) (by omega) h968
      rw [Nat.add_sub_of_le hlast, Nat.zero_add] at he
      exact he.trans (href (j-968) (by omega))
    · let k := (j-16)/32
      let r := (j-16)%32
      have hk : k < 30 := by dsimp [k]; omega
      have hr : r < 32 := Nat.mod_lt _ (by decide)
      have he : 16+32*k+r = j := by dsimp [k,r]; omega
      have hh := byte_eq_of_word input (16+32*k) 0 r hr (hmain k hk)
      rw [he, Nat.zero_add] at hh
      exact hh.trans (href r hr)

#print axioms anchor_byte
#print axioms reference_bytes
#print axioms all_bytes
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PcSeedCoverage
