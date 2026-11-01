import Challenge.Modexp.Submission.Proofs.Fast.ShiftModel
import Challenge.Modexp.Submission.Proofs.Fast.M9MacChain

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def entryWord (n : Nat) : UInt256 :=
  UInt256.ofNat (if n = 4 then 2901 else 2785)

theorem entryWord_eq_entryPC (n : Nat) (hn : n = 4 ∨ n = 8) :
    entryWord n = UInt256.ofNat (M9Mac.entryPC n) := by
  rcases hn with h | h <;> subst h <;> rfl

/-- The conversion entry used to be cached at `0x6a2` (1698); nothing reads it, so the store is
gone and the cache memory is the memory itself. -/
def cacheMem (mem : ByteArray) (_n : Nat) : ByteArray := mem

theorem read_disjoint (mem : ByteArray) (n addr : Nat)
    (h : addr + 32 ≤ 1698 ∨ 1730 ≤ addr) :
    MachineState.readWord (cacheMem mem n) addr = MachineState.readWord mem addr := rfl

theorem represents_cache (mem : ByteArray) (n ptr cnt value : Nat)
    (h : ptr + 32 * cnt ≤ 1698 ∨ 1730 ≤ ptr)
    (hr : Model.FastRepresents mem ptr cnt value) :
    Model.FastRepresents (cacheMem mem n) ptr cnt value := hr

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

end Challenge.Modexp.Submission.Proofs.Fast.ShiftCacheModel
