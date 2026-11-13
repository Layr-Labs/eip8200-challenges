import Challenge.EvmProof.Bytes
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedLaneUInt256Bridge
import Mathlib.Tactic

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolByte
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof PairedLaneUInt256Bridge

def byte (w : UInt256) (i : Nat) : UInt8 :=
  UInt8.ofBitVec ((bits w).extractLsb' (8 * (31-i)) 8)

theorem byte_toNat (w : UInt256) (i : Nat) :
    (byte w i).toNat = w.toNat / 2^(8*(31-i)) % 256 := by
  simp only [byte, UInt8.toNat_ofBitVec, BitVec.extractLsb'_toNat,
    bits_toNat, Nat.shiftRight_eq_div_pow]

theorem encoded (w : UInt256) (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded w.toNat 32)[i]?.getD 0 = byte w i := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  apply UInt8.toNat_inj.mp
  rw [byte_toNat]
  simp only [UInt8.toNat_ofNat', Nat.mod_mod]
  congr 2
  exact (Nat.pow_mul 2 8 (31-i)).symm

theorem byteFrom (m : ByteArray) (a : Nat) :
    YulSemantics.EVM.byteFrom m.toList a = m[a]?.getD 0 := by
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  rfl

theorem read (m : ByteArray) (a i : Nat) (hi : i < 32) :
    byte (MachineState.readWord m a) i = m[a+i]?.getD 0 := by
  apply UInt8.toNat_inj.mp
  rw [byte_toNat]
  have h := Bytes.readWord_shift_toNat m a (i+1) (by omega)
  rw [Nat.shiftRight_eq_div_pow,
    show (32-(i+1))*8 = 8*(31-i) by omega] at h
  rw [h, Bytes.bytesToNatPadded_succ, byteFrom]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt (m[a+i]?.getD 0).toNat_lt]

theorem land (a b : UInt256) (i : Nat) :
    byte (UInt256.land a b) i = byte a i &&& byte b i := by
  apply UInt8.eq_of_toBitVec_eq
  change (bits (UInt256.land a b)).extractLsb' _ _ =
    (bits a).extractLsb' _ _ &&& (bits b).extractLsb' _ _
  rw [bits_land, BitVec.extractLsb'_and]

theorem lor (a b : UInt256) (i : Nat) :
    byte (UInt256.lor a b) i = byte a i ||| byte b i := by
  apply UInt8.eq_of_toBitVec_eq
  change (bits (UInt256.lor a b)).extractLsb' _ _ =
    (bits a).extractLsb' _ _ ||| (bits b).extractLsb' _ _
  rw [bits_lor, BitVec.extractLsb'_or]

theorem shl144 (a : UInt256) (i : Nat) (hi : i < 32) :
    byte (UInt256.shiftLeft a (UInt256.ofNat 144)) i =
      if i < 14 then byte a (i+18) else 0 := by
  apply UInt8.eq_of_toBitVec_eq
  by_cases h14 : i < 14
  · rw [if_pos h14]
    change (bits (UInt256.shiftLeft a (UInt256.ofNat 144))).extractLsb' (8*(31-i)) 8 =
      (bits a).extractLsb' (8*(31-(i+18))) 8
    rw [bits_shl _ _ (by decide)]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hj, decide_true,
      Bool.true_and]
    have h1 : 8 * (31-i) + j < 256 := by omega
    have h2 : 144 ≤ 8 * (31-i) + j := by omega
    have h3 : 8*(31-i)+j-144 = 8*(31-(i+18))+j := by omega
    simp [h1, h2, h3, show ¬ 8*(31-i)+j < 144 by omega]
  · rw [if_neg h14]
    change (bits (UInt256.shiftLeft a (UInt256.ofNat 144))).extractLsb' _ _ = 0#8
    rw [bits_shl _ _ (by decide)]
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_shiftLeft, hj, decide_true,
      Bool.true_and, BitVec.getLsbD_zero]
    have h1 : ¬ 144 ≤ 8*(31-i)+j := by omega
    simp [h1]

@[simp] theorem and255 (a : UInt8) : a &&& 255 = a := by
  apply UInt8.eq_of_toBitVec_eq
  exact BitVec.and_allOnes

@[simp] theorem and0 (a : UInt8) : a &&& 0 = 0 := by
  apply UInt8.eq_of_toBitVec_eq
  exact BitVec.and_zero

@[simp] theorem or0 (a : UInt8) : a ||| 0 = a := by
  apply UInt8.eq_of_toBitVec_eq
  exact BitVec.or_zero

@[simp] theorem zeroOr (a : UInt8) : 0 ||| a = a := by
  apply UInt8.eq_of_toBitVec_eq
  exact BitVec.zero_or

#print axioms read
#print axioms shl144
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolByte
