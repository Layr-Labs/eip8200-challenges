import Challenge.EvmProof.Memory
import Challenge.Modexp.Submission.Proofs.Prepared.Arithmetic
set_option warningAsError true
namespace R9SharedMemory
open EvmSemantics Challenge.EvmProof.Memory
theorem overwrite (mem a b : ByteArray) (start : Nat) (hlen : a.size = b.size) :
    MachineState.writeBytes (MachineState.writeBytes mem a start) b start =
      MachineState.writeBytes mem b start := by
  apply ByteArray.ext_getElem
  · by_cases hz : b.size = 0
    · simp [MachineState.writeBytes_size,hlen,hz]
    · simp [MachineState.writeBytes_size,hlen,hz]
  · intro i hi₁ hi₂
    rw [← getD0_eq_getElem _ _ hi₁,← getD0_eq_getElem _ _ hi₂]
    simp only [MachineState.writeBytes_getElem?_getD,hlen]
    split <;> simp_all
theorem commute (mem a b : ByteArray) (x y : Nat)
    (hsep : x+a.size ≤ y ∨ y+b.size ≤ x) :
    MachineState.writeBytes (MachineState.writeBytes mem a x) b y =
      MachineState.writeBytes (MachineState.writeBytes mem b y) a x := by
  apply ByteArray.ext_getElem
  · by_cases ha : a.size = 0 <;> by_cases hb : b.size = 0 <;>
      simp [MachineState.writeBytes_size,ha,hb,Nat.max_comm,Nat.max_left_comm]
  · intro i hi₁ hi₂
    rw [← getD0_eq_getElem _ _ hi₁,← getD0_eq_getElem _ _ hi₂]
    simp only [MachineState.writeBytes_getElem?_getD]
    by_cases hx : x ≤ i ∧ i < x+a.size
    · have hy : ¬(y ≤ i ∧ i < y+b.size) := by omega
      simp [hx,hy]
    · simp [hx]
theorem word_commute (mem : ByteArray) (a b : UInt256) (x y : Nat)
    (hsep : x+32 ≤ y ∨ y+32 ≤ x) :
    MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded a.toNat 32) x)
      (Data.Bytes.natToBytesPadded b.toNat 32) y =
    MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded b.toNat 32) y)
      (Data.Bytes.natToBytesPadded a.toNat 32) x := by
  apply commute
  simpa only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size] using hsep
theorem word_overwrite (mem : ByteArray) (a b : UInt256) (x : Nat) :
    MachineState.writeBytes (MachineState.writeBytes mem (Data.Bytes.natToBytesPadded a.toNat 32) x)
      (Data.Bytes.natToBytesPadded b.toNat 32) x =
    MachineState.writeBytes mem (Data.Bytes.natToBytesPadded b.toNat 32) x := by
  apply overwrite
  simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
end R9SharedMemory
