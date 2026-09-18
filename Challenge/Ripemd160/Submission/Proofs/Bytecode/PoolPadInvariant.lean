import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolPadInvariant
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem extra_clear (m : ByteArray) (n : UInt256) (hn : n.toNat < 2^64)
    (hlow : (MachineState.readWord m 0).toNat % 2^144 < 2^32) :
    PoolInvariant.ExtraClear (StaggerTablePad.padRealResult m n) := by
  intro a ha
  have hagree := StaggerTablePad.padRealResult_agree m n hlow
  have ha14 : 14 ≤ a := by simp only [List.mem_cons, List.not_mem_nil, or_false] at ha; omega
  rw [hagree.2 a ha14, StaggerTablePad.resultMemory_eq_table m n hn]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*2+24]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*2+25]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*32+18]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*32+19]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*33+20]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*33+21]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*35+18]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl
  · change (StaggerTableMemory.storeDescending m _ 0 61)[18*35+19]?.getD 0 = 0
    rw [StaggerTableMemory.getD_pair _ _ _ _ _ _ (by decide) (by decide) (by decide)]
    simp [StaggerTableLayout.tableWords, StaggerTableLayout.slots, StaggerTablePad.padWordsDirty, PadOnlySchedule.padWords]
    rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ (by decide)]
    rfl

#print axioms extra_clear
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolPadInvariant
