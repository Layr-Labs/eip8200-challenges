import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
open EvmSemantics

/-- Concrete and virtual memory agree away from the cached top word. -/
def Agree (a b : ByteArray) : Prop :=
  ∀ i, i < 2080 ∨ 2112 ≤ i → a[i]?.getD 0 = b[i]?.getD 0

theorem refl (a : ByteArray) : Agree a a := fun _ _ => rfl

theorem symm {a b : ByteArray} (h : Agree a b) : Agree b a :=
  fun i hi => (h i hi).symm

theorem trans {a b c : ByteArray} (hab : Agree a b) (hbc : Agree b c) : Agree a c :=
  fun i hi => (hab i hi).trans (hbc i hi)

theorem readPadded_eq {a b : ByteArray} (h : Agree a b) (start count : Nat)
    (hout : start + count ≤ 2080 ∨ 2112 ≤ start) :
    MachineState.readPadded a start count = MachineState.readPadded b start count := by
  apply Challenge.EvmProof.Memory.readPadded_congr
  intro i hi
  exact h (start + i) (by omega)

theorem readWord_eq {a b : ByteArray} (h : Agree a b) (start : Nat)
    (hout : start + 32 ≤ 2080 ∨ 2112 ≤ start) :
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

theorem top_write (a : ByteArray) (bytes : ByteArray) (hlen : bytes.size = 32) :
    Agree (MachineState.writeBytes a bytes 2080) a := by
  intro i hi
  rw [MachineState.writeBytes_getElem?_getD, if_neg]
  · intro h
    rw [hlen] at h
    omega

theorem top_word (a : ByteArray) (word : UInt256) :
    Agree (MachineState.writeBytes a (Data.Bytes.natToBytesPadded word.toNat 32) 2080) a := by
  apply top_write
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

/-- Materialize the register value in the virtual memory model. -/
def lift (mem : ByteArray) (tn : UInt256) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded tn.toNat 32) 2080

def Invariant (actual ideal : ByteArray) (tn : UInt256) : Prop :=
  Agree actual ideal ∧ tn = MachineState.readWord ideal 2080

/-- Writing the same cached value restores agreement at every byte. -/
theorem flush_agree (a b : ByteArray) (tn : UInt256) (h : Agree a b) :
    ∀ i : Nat, (lift a tn)[i]?.getD 0 = (lift b tn)[i]?.getD 0 := by
  intro i
  unfold lift
  rw [MachineState.writeBytes_getElem?_getD, MachineState.writeBytes_getElem?_getD]
  split
  · rfl
  · next hout =>
      apply h
      have hs : (Data.Bytes.natToBytesPadded tn.toNat 32).size = 32 := by
        simp [Data.Bytes.natToBytesPadded, ByteArray.size]
      rw [hs] at hout
      omega

#print axioms flush_agree

def put (mem : ByteArray) (word : UInt256) (addr : Nat) : ByteArray :=
  MachineState.writeBytes mem (Data.Bytes.natToBytesPadded word.toNat 32) addr

@[simp] theorem wordBytes_size (word : UInt256) :
    (Data.Bytes.natToBytesPadded word.toNat 32).size = 32 := by
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]

theorem put_overwrite (mem : ByteArray) (a b : UInt256) (addr : Nat) :
    put (put mem a addr) b addr = put mem b addr := by
  apply ByteArray.ext_getElem
  · simp only [put, MachineState.writeBytes_size, wordBytes_size]
    split_ifs <;> omega
  · intro i h1 h2
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h1,
        ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h2]
    simp only [put, MachineState.writeBytes_getElem?_getD, wordBytes_size]
    split <;> simp_all

theorem put_comm (mem : ByteArray) (a b : UInt256) (p q : Nat)
    (h : p+32 ≤ q ∨ q+32 ≤ p) :
    put (put mem a p) b q = put (put mem b q) a p := by
  apply ByteArray.ext_getElem
  · simp only [put, MachineState.writeBytes_size, wordBytes_size]
    split_ifs <;> omega
  · intro i h1 h2
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h1,
        ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ h2]
    simp only [put, MachineState.writeBytes_getElem?_getD, wordBytes_size]
    by_cases hp : p ≤ i ∧ i < p+32
    · have hq : ¬(q ≤ i ∧ i < q+32) := by omega
      simp [hp, hq]
    · by_cases hq : q ≤ i ∧ i < q+32
      · simp [hp, hq]
      · simp [hp, hq]

@[simp] theorem read_put (mem : ByteArray) (a : UInt256) (p : Nat) :
    MachineState.readWord (put mem a p) p = a :=
  Challenge.EvmProof.Memory.readWord_writeWord mem p a

theorem read_put_outside (mem : ByteArray) (a : UInt256) (p q : Nat)
    (h : q+32 ≤ p ∨ p+32 ≤ q) :
    MachineState.readWord (put mem a p) q = MachineState.readWord mem q := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa only [wordBytes_size] using h

theorem lift_put (mem : ByteArray) (tn a : UInt256) (p : Nat)
    (h : p+32 ≤ 2080 ∨ 2112 ≤ p) :
    lift (put mem a p) tn = put (lift mem tn) a p :=
  put_comm mem a tn p 2080 h

@[simp] theorem lift_overwrite (mem : ByteArray) (a b : UInt256) :
    lift (lift mem a) b = lift mem b := put_overwrite mem a b 2080

@[simp] theorem read_lift (mem : ByteArray) (tn : UInt256) :
    MachineState.readWord (lift mem tn) 2080 = tn := read_put mem tn 2080

theorem read_lift_outside (mem : ByteArray) (tn : UInt256) (p : Nat)
    (h : p+32 ≤ 2080 ∨ 2112 ≤ p) :
    MachineState.readWord (lift mem tn) p = MachineState.readWord mem p :=
  read_put_outside mem tn 2080 p h

#print axioms put_comm
#print axioms lift_overwrite
end Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
