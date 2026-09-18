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

/-! ## Exact write algebra for the slot channel

The reassembled kernel keeps the row carry in a stack cell and writes the scratch word
`[2080, 2112)` only at the kernel exit (the `DUP9 PUSH2 0x820 MSTORE` flush), while the
reference row model `rowsCarry` writes it every row.  The real memory is therefore the
model memory with the entry word re-installed at 2080 (`unflush`); the lemmas below let
that write commute past every limb store and collapse under the exit flush. -/

theorem writeBytes_comm (bs a b : ByteArray) (s1 s2 : Nat)
    (h : s1 + a.size ≤ s2 ∨ s2 + b.size ≤ s1) :
    MachineState.writeBytes (MachineState.writeBytes bs a s1) b s2 =
      MachineState.writeBytes (MachineState.writeBytes bs b s2) a s1 := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size]
    split_ifs <;> omega
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    simp only [MachineState.writeBytes_getElem?_getD]
    split_ifs <;> first | rfl | omega

theorem writeBytes_absorb (bs a b : ByteArray) (start : Nat) (h : a.size = b.size) :
    MachineState.writeBytes (MachineState.writeBytes bs a start) b start =
      MachineState.writeBytes bs b start := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size]
    split_ifs <;> omega
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    simp only [MachineState.writeBytes_getElem?_getD]
    split_ifs <;> first | rfl | omega

/-- Writing a window back where it was read from is the identity. -/
theorem writeBytes_readPadded_self (m : ByteArray) (start count : Nat)
    (h : start + count ≤ m.size) :
    MachineState.writeBytes m (MachineState.readPadded m start count) start = m := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size, Challenge.EvmProof.Memory.readPadded_size]
    split_ifs <;> omega
  · intro i hi₁ hi₂
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₁,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi₂]
    rw [MachineState.writeBytes_getElem?_getD, Challenge.EvmProof.Memory.readPadded_size]
    split_ifs with hw
    · rw [Challenge.EvmProof.Memory.readPadded_getElem?_getD, if_pos (by omega),
        Nat.add_sub_cancel' hw.1]
    · rfl

/-- The real kernel memory: the model memory with the entry scratch word of `m0`
re-installed at 2080 (the reassembled rows never write that word). -/
def unflush (m0 m : ByteArray) : ByteArray :=
  MachineState.writeBytes m (MachineState.readPadded m0 2080 32) 2080

theorem unflush_self (m0 : ByteArray) (h : 2112 ≤ m0.size) : unflush m0 m0 = m0 :=
  writeBytes_readPadded_self m0 2080 32 h

theorem unflush_writeBytes (m0 m bytes : ByteArray) (start : Nat)
    (h : start + bytes.size ≤ 2080 ∨ 2112 ≤ start) :
    unflush m0 (MachineState.writeBytes m bytes start) =
      MachineState.writeBytes (unflush m0 m) bytes start := by
  unfold unflush
  rw [writeBytes_comm]
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

/-- A write of the scratch word itself is invisible under `unflush`. -/
theorem unflush_writeWord (m0 m : ByteArray) (bytes : ByteArray) (h : bytes.size = 32) :
    unflush m0 (MachineState.writeBytes m bytes 2080) = unflush m0 m := by
  unfold unflush
  rw [writeBytes_absorb]
  rw [h, Challenge.EvmProof.Memory.readPadded_size]

theorem readWord_unflush (m0 m : ByteArray) (addr : Nat)
    (h : addr + 32 ≤ 2080 ∨ 2112 ≤ addr) :
    MachineState.readWord (unflush m0 m) addr = MachineState.readWord m addr := by
  unfold unflush
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

theorem readPadded_unflush (m0 m : ByteArray) (start count : Nat)
    (h : start + count ≤ 2080 ∨ 2112 ≤ start) :
    MachineState.readPadded (unflush m0 m) start count = MachineState.readPadded m start count := by
  unfold unflush
  apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega

/-- The exit flush re-installs the model's scratch word: when the model memory's last
write was that word, flushing it over the real memory reproduces the model exactly. -/
theorem flush_unflush (m0 m bytes : ByteArray) (h : bytes.size = 32) :
    MachineState.writeBytes (unflush m0 (MachineState.writeBytes m bytes 2080)) bytes 2080 =
      MachineState.writeBytes m bytes 2080 := by
  rw [unflush_writeWord m0 m bytes h]
  unfold unflush
  rw [writeBytes_absorb]
  rw [h, Challenge.EvmProof.Memory.readPadded_size]

end Challenge.Modexp.Submission.Proofs.Fast.CarryScratchAgreement
