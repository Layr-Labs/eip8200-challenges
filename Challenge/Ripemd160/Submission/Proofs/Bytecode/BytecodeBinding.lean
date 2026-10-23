import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Bytecode
set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000

/-!
# Exact-byte binding for the current hoisted-store image

The protected artifact is regenerated from the submitted `bytecode.hex`.
`HoistedInherited.submissionBytecode` is the candidate-bound literal used in
`HoistedStoreCorrect.correct`. Historical `Submission/Bytes.lean` remains the
predecessor literal for archived proof modules and is not the current image.
Kernel definitional equality, rather than a hash comparison, binds all bytes.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.BytecodeBinding

open Challenge.Ripemd160

theorem exact : Benchmark.bytecode = HoistedInherited.submissionBytecode := by
  rfl

end Challenge.Ripemd160.Submission.Proofs.Bytecode.BytecodeBinding
