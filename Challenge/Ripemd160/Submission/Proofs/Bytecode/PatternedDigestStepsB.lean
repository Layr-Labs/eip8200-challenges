import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic04
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic05
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic06
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic07
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestB
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps

open EvmSemantics.Crypto PatternedDigest PatternedInputData

theorem step4 : Ripemd160.compressBlock (knownAt 4)
    (Padding.paddedMessage patternedInput) 256 = knownAt 5 := by
  change Ripemd160.compressBlock H4
    (Padding.paddedMessage patternedInput) 256 = H5
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H4 _ _ 256 (by
    rw [patternedInput_size]; omega),
    compress4 H4, PatternedDigestB.step4]

theorem step5 : Ripemd160.compressBlock (knownAt 5)
    (Padding.paddedMessage patternedInput) 320 = knownAt 6 := by
  change Ripemd160.compressBlock H5
    (Padding.paddedMessage patternedInput) 320 = H6
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H5 _ _ 320 (by
    rw [patternedInput_size]; omega),
    compress5 H5, PatternedDigestB.step5]

theorem step6 : Ripemd160.compressBlock (knownAt 6)
    (Padding.paddedMessage patternedInput) 384 = knownAt 7 := by
  change Ripemd160.compressBlock H6
    (Padding.paddedMessage patternedInput) 384 = H7
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H6 _ _ 384 (by
    rw [patternedInput_size]; omega),
    compress6 H6, PatternedDigestB.step6]

theorem step7 : Ripemd160.compressBlock (knownAt 7)
    (Padding.paddedMessage patternedInput) 448 = knownAt 8 := by
  change Ripemd160.compressBlock H7
    (Padding.paddedMessage patternedInput) 448 = H8
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H7 _ _ 448 (by
    rw [patternedInput_size]; omega),
    compress7 H7, PatternedDigestB.step7]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps
