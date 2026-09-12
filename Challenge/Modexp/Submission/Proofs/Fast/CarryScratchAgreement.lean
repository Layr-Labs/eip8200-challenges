import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryScratchAgreement
open EvmSemantics

/-- The scratch word8192 is not part of the persistent operand or result region. -/
def Agree (a b : ByteArray) : Prop :=
  ∀ i, i < 2048 ∨ 2080 ≤ i → a[i]?.getD 0 = b[i]?.getD 0

theorem refl (a : ByteArray) : Agree a a := fun _ _ => rfl

theorem symm {a b : ByteArray} (h : Agree a b) : Agree b a :=
  fun i hi => (h i hi).symm

theorem trans {a b c : ByteArray} (hab : Agree a b) (hbc : Agree b c) : Agree a c :=
  fun i hi => (hab i hi).trans (hbc i hi)

theorem readPadded_eq {a b : ByteArray} (h : Agree a b) (start count : Nat)
    (hout : start + count ≤ 2048 ∨ 2080 ≤ start) :
    MachineState.readPadded a start count = MachineState.readPadded b start count := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  exact h (start + i) (by omega)

theorem readWord_eq {a b : ByteArray} (h : Agree a b) (start : Nat)
    (hout : start + 32 ≤ 2048 ∨ 2080 ≤ start) :
    MachineState.readWord a start = MachineState.readWord b start := by
  unfold MachineState.readWord
  rw [readPadded_eq h start 32 hout]

theorem write_same {a b : ByteArray} (h : Agree a b) (bytes : ByteArray) (start : Nat) :
    Agree (MachineState.writeBytes a bytes start) (MachineState.writeBytes b bytes start) := by
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD]
  split
  · rfl
  · exact h i hi

theorem scratch_write (a : ByteArray) (bytes : ByteArray) (hlen : bytes.size = 32) :
    Agree (MachineState.writeBytes a bytes 2048) a := by
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, if_neg]
  · intro h
    rw [hlen] at h
    omega

theorem scratch_word (a : ByteArray) (word : UInt256) :
    Agree (MachineState.writeBytes a (Data.Bytes.natToBytesPadded word.toNat 32) 2048) a := by
  apply scratch_write
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

end Challenge.Modexp.Submission.Proofs.Fast.CarryScratchAgreement
