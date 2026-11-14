import Challenge.Modexp.Submission.Proofs.Fast.TnCacheMemory
import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.LazyTopMemory
open EvmSemantics
open Challenge.Modexp.Submission.Proofs.Fast
open TnCacheMemory
structure Related (a b : ByteArray) : Prop where
  agree : Agree a b
  size : a.size = b.size
theorem overwrite_eq {a b : ByteArray} (h : Related a b) (bytes : ByteArray)
    (hlen : 32 ≤ bytes.size) :
    MachineState.writeBytes a bytes 2080 = MachineState.writeBytes b bytes 2080 := by
  apply ByteArray.ext_getElem
  · simp only [MachineState.writeBytes_size,h.size]
  · intro i hi hj
    rw [← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hi,
      ← Challenge.EvmProof.Memory.getD0_eq_getElem _ _ hj]
    rw [MachineState.writeBytes_getElem?_getD,MachineState.writeBytes_getElem?_getD]
    split
    · rfl
    · next hout => exact h.agree i (by omega)
theorem mcopy_eq {a b : ByteArray} (h : Related a b) (n : Nat) (hn : 1 ≤ n) :
    Exp.mcopyMem a 2080 2112 (32*n) = Exp.mcopyMem b 2080 2112 (32*n) := by
  unfold Exp.mcopyMem
  rw [readPadded_eq h.agree 2112 (32*n) (Or.inr (by omega))]
  apply overwrite_eq h
  rw [Challenge.EvmProof.Memory.readPadded_size]
  omega
theorem uMem_eq {a b : ByteArray} (h : Related a b) (n : Nat) (hn : 1 ≤ n) :
    Shift.uMem a n = Shift.uMem b n := by
  unfold Shift.uMem
  rw [mcopy_eq h n hn]
theorem store_related (mem : ByteArray) (word : UInt256) (hsize : 2112 ≤ mem.size) :
    Related mem (Exp.storeWord mem 2080 word) := by
  refine ⟨symm (top_word mem word),?_⟩
  unfold Exp.storeWord
  simp only [MachineState.writeBytes_size,wordBytes_size]
  split_ifs <;> omega
theorem uMem_size (mem : ByteArray) (n : Nat) (hn : 1 ≤ n) :
    2112 ≤ (Shift.uMem mem n).size := by
  unfold Shift.uMem Exp.storeWord Exp.mcopyMem
  simp only [MachineState.writeBytes_size,wordBytes_size,
    Challenge.EvmProof.Memory.readPadded_size]
  split_ifs <;> omega
theorem l1_size (mem : ByteArray) (q : UInt256) (pa n j : Nat) :
    mem.size ≤ (Monpro.l1Step mem q pa n j).memory.size := by
  induction j with
  | zero => exact le_refl _
  | succ j ih =>
    simp only [Monpro.l1Step,MachineState.writeBytes_size,wordBytes_size]
    split_ifs <;> omega
theorem stepMem_eq {a b : ByteArray} (h : Related a b) (n mm : Nat) (hn : 1 ≤ n) :
    Shift.stepMem a n mm = Shift.stepMem b n mm := by
  unfold Shift.stepMem
  rw [uMem_eq h n hn]
#print axioms stepMem_eq
end CycleSubmission.Global.LazyTopMemory
