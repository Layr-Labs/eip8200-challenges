import Challenge.RouteB.Bytecode
import EvmSemantics.Machine.MachineState
set_option warningAsError true
/-!
# Pointwise EVM memory reasoning

Reusable bridges from the executable `ByteArray` memory helpers to list and
pointwise views suitable for functional bytecode proofs.
-/

namespace Challenge.RouteB.Memory

open EvmSemantics

theorem readPadded_toList (bs : ByteArray) (start n : Nat) :
    (MachineState.readPadded bs start n).toList =
      (bs.data.toList.drop (min start bs.size)).take
          (min (bs.size - min start bs.size) n) ++
        List.replicate (n - min (bs.size - min start bs.size) n) 0 := by
  simp [MachineState.readPadded, Challenge.RouteB.Bytecode.toList_eq_data,
    ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop]

theorem writeBytes_extract_same (bs bytes : ByteArray) (start : Nat) :
    (MachineState.writeBytes bs bytes start).extract start (start + bytes.size) =
      bytes := by
  apply ByteArray.ext
  apply Array.ext
  · rw [ByteArray.data_extract, Array.size_extract]
    change min (start + bytes.size)
      (MachineState.writeBytes bs bytes start).size - start = bytes.size
    rw [MachineState.writeBytes_size]
    split <;> omega
  · intro i hi₁ hi₂
    simp only [ByteArray.data_extract] at hi₁ ⊢
    rw [Array.getElem_extract]
    have hi₂' : i < bytes.size := hi₂
    have h := MachineState.writeBytes_getElem?_getD bs bytes start (start + i)
    rw [if_pos (by omega)] at h
    have hn : bytes.size ≠ 0 := by omega
    have hw : start + i < (MachineState.writeBytes bs bytes start).size := by
      rw [MachineState.writeBytes_size, if_neg hn]
      omega
    rw [Nat.add_sub_cancel_left] at h
    change ((MachineState.writeBytes bs bytes start).data[start + i]?).getD 0 =
      (bytes.data[i]?).getD 0 at h
    have hw' : start + i < (MachineState.writeBytes bs bytes start).data.size := hw
    rw [Array.getElem?_eq_getElem hw', Array.getElem?_eq_getElem hi₂] at h
    simp only [Option.getD_some] at h
    exact h

theorem readPadded_writeBytes_same (bs bytes : ByteArray) (start : Nat) :
    MachineState.readPadded (MachineState.writeBytes bs bytes start)
      start bytes.size = bytes := by
  unfold MachineState.readPadded
  rw [MachineState.writeBytes_size]
  by_cases hz : bytes.size = 0
  · have hb : bytes = ByteArray.empty := by
      apply ByteArray.ext
      apply Array.ext <;> simp [hz]
    subst bytes
    simp [MachineState.writeBytes]
    apply ByteArray.ext
    rfl
  · simp only [hz, if_false]
    have hsize : start ≤ max bs.size (start + bytes.size) := by omega
    have havail : bytes.size ≤ max bs.size (start + bytes.size) - start := by omega
    simp only [Nat.min_eq_left hsize, Nat.min_eq_right havail,
      Nat.sub_self, Array.replicate_zero, writeBytes_extract_same]
    apply ByteArray.ext
    simp

theorem readWord_writeBytes (bs : ByteArray) (start value : Nat) :
    MachineState.readWord
        (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded value 32) start)
        start =
      UInt256.ofNat
        (Data.Bytes.bytesToBigEndianNat (Data.Bytes.natToBytesPadded value 32)) := by
  unfold MachineState.readWord
  have hsize : (Data.Bytes.natToBytesPadded value 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  have hr := readPadded_writeBytes_same bs
    (Data.Bytes.natToBytesPadded value 32) start
  have hr32 : MachineState.readPadded
      (MachineState.writeBytes bs (Data.Bytes.natToBytesPadded value 32) start)
      start 32 = Data.Bytes.natToBytesPadded value 32 := by
    simpa only [hsize] using hr
  rw [hr32]

end Challenge.RouteB.Memory
