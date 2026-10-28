import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreArtifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Bytecode
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreBinding
/-- The independently chunked inherited-proof image is exactly the measured
hoisted candidate, not merely a same-length or same-hash image. -/
theorem inherited_exact : HoistedInherited.submissionBytecode = HoistedStoreArtifact.code := by
  rfl
#print axioms inherited_exact
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreBinding
