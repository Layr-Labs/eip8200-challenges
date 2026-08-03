import EvmSemantics.Data.Bytes
import Mathlib.Tactic.Ring
import YulEvmCompiler.StateRel
set_option warningAsError true
set_option maxRecDepth 10000
/-!
# Big-endian byte arithmetic

Reusable algebra for the fold shared by CALLDATALOAD, MODEXP, and fixed-width
encoders.  These lemmas deliberately mention only lists of bytes.
-/

namespace Challenge.EvmProof.Bytes

open EvmSemantics

def step (acc : Nat) (byte : UInt8) : Nat :=
  acc * 256 + byte.toNat

def bytesNat (bytes : List UInt8) : Nat :=
  bytes.foldl step 0

theorem bytesNat_toList (bytes : ByteArray) :
    bytesNat bytes.toList = Data.Bytes.bytesToBigEndianNat bytes := rfl

theorem memMatch_toList (bytes : ByteArray) :
    YulEvmCompiler.MemMatch
      (YulSemantics.EVM.byteFrom bytes.toList) bytes := by
  intro i
  rw [YulEvmCompiler.ByteArray.toList_eq_data]
  unfold YulSemantics.EVM.byteFrom
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList]
  by_cases hi : i < bytes.size
  · rw [dif_pos hi, Array.getElem?_eq_getElem (by exact hi)]
    rfl
  · have hnone : bytes.data.size ≤ i := by
      change ¬i < bytes.data.size at hi
      omega
    rw [dif_neg hi, Array.getElem?_eq_none_iff.mpr hnone]
    rfl

theorem readPadded_toList (bytes : ByteArray) (offset width : Nat) :
    (EvmSemantics.MachineState.readPadded bytes offset width).toList =
      (List.range width).map
        (fun i => YulSemantics.EVM.byteFrom bytes.toList (offset + i)) := by
  exact (memMatch_toList bytes).readBytes offset width |>.symm

theorem readPadded_toList_succ (bytes : ByteArray) (offset width : Nat) :
    (EvmSemantics.MachineState.readPadded bytes offset (width + 1)).toList =
      (EvmSemantics.MachineState.readPadded bytes offset width).toList ++
        [YulSemantics.EVM.byteFrom bytes.toList (offset + width)] := by
  rw [readPadded_toList, readPadded_toList, List.range_succ, List.map_append]
  rfl

theorem foldl_step (bytes : List UInt8) (acc : Nat) :
    bytes.foldl step acc =
      acc * 256 ^ bytes.length + bytes.foldl step 0 := by
  induction bytes generalizing acc with
  | nil => simp
  | cons byte bytes ih =>
    rw [List.foldl_cons, ih, List.length_cons, Nat.pow_succ]
    rw [List.foldl_cons]
    simp only [step, Nat.zero_mul, Nat.zero_add]
    rw [ih byte.toNat]
    ring

theorem bytesNat_append (left right : List UInt8) :
    bytesNat (left ++ right) =
      bytesNat left * 256 ^ right.length + bytesNat right := by
  unfold bytesNat
  rw [List.foldl_append]
  exact foldl_step right (left.foldl step 0)

theorem bytesNat_cons (byte : UInt8) (bytes : List UInt8) :
    bytesNat (byte :: bytes) =
      byte.toNat * 256 ^ bytes.length + bytesNat bytes := by
  simpa [bytesNat, step] using bytesNat_append [byte] bytes

theorem bytesNat_snoc (bytes : List UInt8) (byte : UInt8) :
    bytesNat (bytes ++ [byte]) = bytesNat bytes * 256 + byte.toNat := by
  rw [bytesNat_append]
  simp [bytesNat, step]

theorem bytesToNatPadded_succ (bytes : ByteArray) (offset width : Nat) :
    EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset (width + 1) =
      EvmSemantics.EVM.Precompile.bytesToNatPadded bytes offset width * 256 +
        (YulSemantics.EVM.byteFrom bytes.toList (offset + width)).toNat := by
  unfold EvmSemantics.EVM.Precompile.bytesToNatPadded
  rw [← bytesNat_toList, readPadded_toList_succ, bytesNat_snoc,
    bytesNat_toList]

theorem bytesNat_lt_pow (bytes : List UInt8) :
    bytesNat bytes < 256 ^ bytes.length := by
  induction bytes with
  | nil => simp [bytesNat]
  | cons byte bytes ih =>
    rw [bytesNat_cons, List.length_cons, Nat.pow_succ]
    have hbyte : byte.toNat < 256 := byte.toNat_lt
    have hpow : 0 < 256 ^ bytes.length := Nat.pow_pos (by omega)
    calc
      byte.toNat * 256 ^ bytes.length + bytesNat bytes <
          byte.toNat * 256 ^ bytes.length + 256 ^ bytes.length :=
        Nat.add_lt_add_left ih _
      _ = (byte.toNat + 1) * 256 ^ bytes.length := by ring
      _ ≤ 256 * 256 ^ bytes.length :=
        Nat.mul_le_mul_right _ (by omega)
      _ = 256 ^ bytes.length * 256 := Nat.mul_comm _ _

end Challenge.EvmProof.Bytes
