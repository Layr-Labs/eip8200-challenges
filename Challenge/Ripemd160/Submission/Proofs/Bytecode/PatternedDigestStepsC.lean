import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic08
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic09
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic10
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic11
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps

open EvmSemantics.Crypto PatternedDigest PatternedInputData

theorem step8 : Ripemd160.compressBlock (knownAt 8)
    (Padding.paddedMessage patternedInput) 512 = knownAt 9 := by
  change Ripemd160.compressBlock H8
    (Padding.paddedMessage patternedInput) 512 = H9
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H8 _ _ 512 (by
    rw [patternedInput_size]; omega),
    compress8 H8, PatternedDigestC.step8]

theorem step9 : Ripemd160.compressBlock (knownAt 9)
    (Padding.paddedMessage patternedInput) 576 = knownAt 10 := by
  change Ripemd160.compressBlock H9
    (Padding.paddedMessage patternedInput) 576 = H10
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H9 _ _ 576 (by
    rw [patternedInput_size]; omega),
    compress9 H9, PatternedDigestC.step9]

theorem step10 : Ripemd160.compressBlock (knownAt 10)
    (Padding.paddedMessage patternedInput) 640 = knownAt 11 := by
  change Ripemd160.compressBlock H10
    (Padding.paddedMessage patternedInput) 640 = H11
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H10 _ _ 640 (by
    rw [patternedInput_size]; omega),
    compress10 H10, PatternedDigestC.step10]

theorem step11 : Ripemd160.compressBlock (knownAt 11)
    (Padding.paddedMessage patternedInput) 704 = knownAt 12 := by
  change Ripemd160.compressBlock H11
    (Padding.paddedMessage patternedInput) 704 = H12
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H11 _ _ 704 (by
    rw [patternedInput_size]; omega),
    compress11 H11, PatternedDigestC.step11]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps
