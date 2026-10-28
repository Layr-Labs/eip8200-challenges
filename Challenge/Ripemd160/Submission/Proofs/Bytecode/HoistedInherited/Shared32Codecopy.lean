import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32SparseRun
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Codecopy
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open HoistedInherited.Shared32Scratch PairedScheduleMemory

theorem copied_eq (m : ByteArray) :
    HoistedInherited.Shared32SparseRun.copied m HoistedInherited.Artifact.submissionArtifact.code = writeWord m 162 highWord := by
  rfl

theorem copied_sparse (m : ByteArray) (hsize : 194 ≤ m.size)
    (hzero : ∀ a, 162 ≤ a → a < 194 → m[a]?.getD 0 = 0) :
    HoistedInherited.Shared32SparseRun.copied m HoistedInherited.Artifact.submissionArtifact.code = sparseMemory m := by
  rw [copied_eq, sparse_eq_writeWord m hsize hzero]
#print axioms copied_sparse
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Codecopy
