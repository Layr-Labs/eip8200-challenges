import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32SparseRun
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Codecopy
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Shared32Scratch PairedScheduleMemory

theorem copied_eq (m : ByteArray) :
    Shared32SparseRun.copied m Artifact.submissionArtifact.code = writeWord m 162 highWord := by
  rfl

theorem copied_sparse (m : ByteArray) (hsize : 194 ≤ m.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → m[a]?.getD 0 = 0) :
    Shared32SparseRun.copied m Artifact.submissionArtifact.code = sparseMemory m := by
  rw [copied_eq, sparse_eq_writeWord m hsize hzero]
#print axioms copied_sparse
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Codecopy
