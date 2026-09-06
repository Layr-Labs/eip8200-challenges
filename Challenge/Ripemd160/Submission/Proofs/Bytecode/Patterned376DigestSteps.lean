import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestB
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Padding

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestSteps

open EvmSemantics.Crypto Patterned376Digest Patterned376InputData

theorem step0 : Ripemd160.compressBlock (knownAt 0)
    (Padding.paddedMessage patterned376Input) 0 = knownAt 1 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H0 paddedLiteral 0 = H1
  rw [compress0 H0, Patterned376DigestA.step0]
theorem step1 : Ripemd160.compressBlock (knownAt 1)
    (Padding.paddedMessage patterned376Input) 64 = knownAt 2 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H1 paddedLiteral 64 = H2
  rw [compress1 H1, Patterned376DigestA.step1]
theorem step2 : Ripemd160.compressBlock (knownAt 2)
    (Padding.paddedMessage patterned376Input) 128 = knownAt 3 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H2 paddedLiteral 128 = H3
  rw [compress2 H2, Patterned376DigestA.step2]
theorem step3 : Ripemd160.compressBlock (knownAt 3)
    (Padding.paddedMessage patterned376Input) 192 = knownAt 4 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H3 paddedLiteral 192 = H4
  rw [compress3 H3, Patterned376DigestA.step3]
theorem step4 : Ripemd160.compressBlock (knownAt 4)
    (Padding.paddedMessage patterned376Input) 256 = knownAt 5 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H4 paddedLiteral 256 = H5
  rw [compress4 H4, Patterned376DigestB.step4]
theorem step5 : Ripemd160.compressBlock (knownAt 5)
    (Padding.paddedMessage patterned376Input) 320 = knownAt 6 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H5 paddedLiteral 320 = H6
  rw [compress5 H5, Patterned376DigestB.step5]
theorem step6 : Ripemd160.compressBlock (knownAt 6)
    (Padding.paddedMessage patterned376Input) 384 = knownAt 7 := by
  rw [paddedMessage_eq]
  change Ripemd160.compressBlock H6 paddedLiteral 384 = H7
  rw [compress6 H6, Patterned376DigestB.step6]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestSteps
