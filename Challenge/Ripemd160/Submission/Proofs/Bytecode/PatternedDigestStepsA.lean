import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic00
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic01
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic02
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic03
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps

open EvmSemantics.Crypto PatternedDigest PatternedInputData

theorem step0 : Ripemd160.compressBlock (knownAt 0)
    (Padding.paddedMessage patternedInput) 0 = knownAt 1 := by
  change Ripemd160.compressBlock H0
    (Padding.paddedMessage patternedInput) 0 = H1
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H0 _ _ 0 (by
    rw [patternedInput_size]; omega),
    compress0 H0, PatternedDigestA.step0]

theorem step1 : Ripemd160.compressBlock (knownAt 1)
    (Padding.paddedMessage patternedInput) 64 = knownAt 2 := by
  change Ripemd160.compressBlock H1
    (Padding.paddedMessage patternedInput) 64 = H2
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H1 _ _ 64 (by
    rw [patternedInput_size]; omega),
    compress1 H1, PatternedDigestA.step1]

theorem step2 : Ripemd160.compressBlock (knownAt 2)
    (Padding.paddedMessage patternedInput) 128 = knownAt 3 := by
  change Ripemd160.compressBlock H2
    (Padding.paddedMessage patternedInput) 128 = H3
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H2 _ _ 128 (by
    rw [patternedInput_size]; omega),
    compress2 H2, PatternedDigestA.step2]

theorem step3 : Ripemd160.compressBlock (knownAt 3)
    (Padding.paddedMessage patternedInput) 192 = knownAt 4 := by
  change Ripemd160.compressBlock H3
    (Padding.paddedMessage patternedInput) 192 = H4
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H3 _ _ 192 (by
    rw [patternedInput_size]; omega),
    compress3 H3, PatternedDigestA.step3]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps
