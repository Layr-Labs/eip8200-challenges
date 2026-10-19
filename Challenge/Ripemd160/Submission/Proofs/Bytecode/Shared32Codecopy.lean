import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Codecopy
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Shared32Scratch PairedScheduleMemory

theorem source_word : MachineState.readPadded Artifact.submissionArtifact.code 5000 32 =
    Data.Bytes.natToBytesPadded highWord.toNat 32 := by
  rw [highWord_bytes]
  apply ByteArray.ext_getElem
  · simp only [Memory.readPadded_size]; rfl
  · intro i hi hj
    have hil : i < 32 := by simpa only [Memory.readPadded_size] using hi
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj,
      Memory.readPadded_getElem?_getD, if_pos hil]
    interval_cases i <;> rfl

theorem copied_eq (m : ByteArray) :
    Shared32SparseRun.copied m Artifact.submissionArtifact.code = writeWord m 162 highWord := by
  rw [Shared32SparseRun.copied, source_word]
  rfl

theorem copied_sparse (m : ByteArray) (hsize : 194 ≤ m.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → m[a]?.getD 0 = 0) :
    Shared32SparseRun.copied m Artifact.submissionArtifact.code = sparseMemory m := by
  rw [copied_eq, sparse_eq_writeWord m hsize hzero]
#print axioms source_word
#print axioms copied_sparse
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Codecopy
