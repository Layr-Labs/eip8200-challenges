import Challenge.Modexp.Submission.Proofs.Fast.ShiftUnrollEntry
import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

abbrev entryWord := ShiftUnrollEntry.entryWord

def cacheMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.storeWord mem 1698 (entryWord n)

theorem read_cache (mem : ByteArray) (n : Nat) :
    MachineState.readWord (cacheMem mem n) 1698 = entryWord n := by
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem read_disjoint (mem : ByteArray) (n addr : Nat)
    (h : addr + 32 ≤ 1698 ∨ 1730 ≤ addr) :
    MachineState.readWord (cacheMem mem n) addr = MachineState.readWord mem addr := by
  exact Exp.storeWord_readWord_disjoint mem 1698 addr (entryWord n) h

theorem represents_cache (mem : ByteArray) (n ptr cnt value : Nat)
    (h : ptr + 32 * cnt ≤ 1698 ∨ 1730 ≤ ptr)
    (hr : Model.FastRepresents mem ptr cnt value) :
    Model.FastRepresents (cacheMem mem n) ptr cnt value := by
  exact Model.fastRepresents_writeWord_disjoint mem 1698 ptr cnt value (entryWord n).toNat
    (Or.symm h) hr

theorem cache_survives_step (mem : ByteArray) (n mm : Nat) (hn : 1 ≤ n) (hcap : n ≤ 8)
    (h : MachineState.readWord mem 1698 = entryWord n) :
    MachineState.readWord (Shift.stepMem mem n mm) 1698 = entryWord n := by
  rw [Shift.stepMem_readWord_disjoint mem n mm 1698 hn
    ⟨Or.inr (by omega), Or.inl (by omega), Or.inl (by omega)⟩]
  exact h

theorem cache_survives_u (mem : ByteArray) (n : Nat)
    (h : MachineState.readWord mem 1698 = entryWord n) :
    MachineState.readWord (Shift.uMem mem n) 1698 = entryWord n := by
  rw [Shift.uMem_readWord_disjoint mem n 1698 (Or.inl (by omega))]
  exact h

#print axioms read_cache
#print axioms represents_cache
#print axioms cache_survives_step
end Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
