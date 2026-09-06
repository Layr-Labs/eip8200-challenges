import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Digest
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionCorrect

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestB

open Patterned376Digest

theorem step4 : CompressionCorrect.normalizedCompress H4 block4 = H5 := by decide
theorem step5 : CompressionCorrect.normalizedCompress H5 block5 = H6 := by decide
theorem step6 : CompressionCorrect.normalizedCompress H6 block6 = H7 := by decide

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestB
