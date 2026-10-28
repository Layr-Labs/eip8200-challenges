import Challenge.Ripemd160.Submission.Local20261028.RecArtifact
import Challenge.Ripemd160.Submission.Local20261028.ColdBytecode
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreBinding
/-- The independently chunked inherited-proof image is exactly the measured
hoisted candidate, not merely a same-length or same-hash image. -/
theorem inherited_exact : Control.submissionBytecode = HoistedStoreArtifact.code := by
  rfl
#print axioms inherited_exact
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreBinding
