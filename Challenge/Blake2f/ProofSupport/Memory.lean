import Challenge.Blake2f.ProofSupport.Algorithm
import Challenge.EvmProof.Memory

set_option warningAsError true

/-!
# Reusable word-oriented memory view

BLAKE2f bytecodes commonly keep each 64-bit lane in a full EVM memory word.
These definitions hide the byte-array encoding and provide the same/disjoint
read lemmas needed to relate such layouts to the pure algorithm model.
-/

namespace Challenge.Blake2f.ProofSupport.Memory

open EvmSemantics

def storeWord (memory : ByteArray) (offset : Nat) (value : UInt256) : ByteArray :=
  MachineState.writeBytes memory
    (Data.Bytes.natToBytesPadded value.toNat 32) offset

def WordDisjoint (a b : Nat) : Prop := a + 32 ≤ b ∨ b + 32 ≤ a

theorem WordDisjoint.symm {a b : Nat} (h : WordDisjoint a b) :
    WordDisjoint b a := by
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

@[simp] theorem readWord_storeWord_same (memory : ByteArray) (offset : Nat)
    (value : UInt256) :
    MachineState.readWord (storeWord memory offset value) offset = value := by
  exact Challenge.EvmProof.Memory.readWord_writeWord memory offset value

theorem readWord_storeWord_disjoint (memory : ByteArray) (readStart writeStart : Nat)
    (value : UInt256) (h : WordDisjoint readStart writeStart) :
    MachineState.readWord (storeWord memory writeStart value) readStart =
      MachineState.readWord memory readStart := by
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simpa [WordDisjoint, Data.Bytes.natToBytesPadded, ByteArray.size] using h

/-- Four word-aligned lanes projected from arbitrary byte-array memory. -/
def lanesAtWords (memory : ByteArray) (a b c d : Nat) :
    Algorithm.Lanes UInt256 :=
  ⟨MachineState.readWord memory a, MachineState.readWord memory b,
    MachineState.readWord memory c, MachineState.readWord memory d⟩

/-- A 64-bit array represented by consecutive 32-byte EVM words. -/
def RepresentsAt (memory : ByteArray) (base : Nat) (values : Array UInt64) : Prop :=
  ∀ i, i < values.size →
    MachineState.readWord memory (base + 32 * i) =
      Word.ofUInt64 values[i]!

/-- Distinct slots in the consecutive 32-byte layout never overlap. -/
theorem wordDisjoint_slots (base i j : Nat) (hij : i ≠ j) :
    WordDisjoint (base + 32 * i) (base + 32 * j) := by
  unfold WordDisjoint
  omega

/-- Projecting represented slots produces the embedded algorithm lanes. -/
theorem lanesAtWords_of_representsAt {memory : ByteArray} {base : Nat}
    {values : Array UInt64} (represents : RepresentsAt memory base values)
    (a b c d : Nat) (ha : a < values.size) (hb : b < values.size)
    (hc : c < values.size) (hd : d < values.size) :
    lanesAtWords memory (base + 32 * a) (base + 32 * b)
        (base + 32 * c) (base + 32 * d) =
      (Algorithm.lanesAt values a b c d).embed := by
  apply Algorithm.Lanes.ext <;>
    simp only [lanesAtWords, Algorithm.lanesAt, Algorithm.Lanes.embed]
  · exact represents a ha
  · exact represents b hb
  · exact represents c hc
  · exact represents d hd

end Challenge.Blake2f.ProofSupport.Memory
