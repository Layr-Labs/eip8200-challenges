import Challenge.Ripemd160.Submission.Local20261028.PadMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

def scalar (n : Fin 3) (k : Nat) : UInt32 :=
  UInt32.ofNat (if k = 0 then 128 else if k = 14 then 64*(n.val+1)*8 else 0)

theorem clean_words (n : Fin 3) (k : Nat) (hk : k < 16) :
    StaggerTablePad.padWordsDirty (PadMemory.length n) k = Word.ofUInt32 (scalar n k) := by
  have closed : ∀ n : Fin 3, ∀ k : Fin 16,
      StaggerTablePad.padWordsDirty (PadMemory.length n) k.val = Word.ofUInt32 (scalar n k.val) := by decide
  exact closed n ⟨k,hk⟩

theorem memory_eq_table (n : Fin 3) :
    PadMemory.memory n = StaggerTableLayout.resultMemory ByteArray.empty
      (StaggerTablePad.padWordsDirty (PadMemory.length n)) := by
  have hzero : StaggerTableSparse.zeroSuffix ByteArray.empty =
      StaggerTableSparse.zeroMemory ByteArray.empty := by
    apply ByteArray.ext_getElem
    · simp [StaggerTableSparse.zeroSuffix_size]
    · intro i hi hj
      rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj,
        StaggerTableSparse.zeroSuffix_getD, StaggerTableSparse.zeroMemory_getD]
      have hempty : (ByteArray.empty[i]?).getD 0 = 0 := rfl
      simp only [hempty, ite_self]
  have hhigh : StaggerTablePad.highDirty (PadMemory.length n) = UInt256.ofNat 0 := by
    have closed : ∀ n : Fin 3, StaggerTablePad.highDirty (PadMemory.length n) = UInt256.ofNat 0 := by decide
    exact closed n
  have hfit : (PadMemory.length n).toNat < 2^64 := by
    have closed : ∀ n : Fin 3, (PadMemory.length n).toNat < 2^64 := by decide
    exact closed n
  unfold PadMemory.memory StaggerTablePad.padRealChain
  rw [hzero, ← StaggerTablePad.lowChain_eq_over,
    StaggerTablePad.lowChain_eq _ _ hhigh, StaggerTablePad.resultMemory_eq_table _ _ hfit]

theorem ready (n : Fin 3) : StaggerMessage.Ready (PadMemory.memory n) (scalar n) := by
  rw [memory_eq_table]
  exact StaggerMessage.ready _ _ _ (clean_words n)

#print axioms clean_words
#print axioms memory_eq_table
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PadReady
