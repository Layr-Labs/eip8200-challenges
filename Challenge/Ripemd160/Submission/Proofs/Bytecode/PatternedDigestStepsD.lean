import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic12
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic13
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic14
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogicFinal
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps

open EvmSemantics.Crypto PatternedDigest PatternedInputData

theorem step12 : Ripemd160.compressBlock (knownAt 12)
    (Padding.paddedMessage patternedInput) 768 = knownAt 13 := by
  change Ripemd160.compressBlock H12
    (Padding.paddedMessage patternedInput) 768 = H13
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H12 _ _ 768 (by
    rw [patternedInput_size]; omega),
    compress12 H12, PatternedDigestD.step12]

theorem step13 : Ripemd160.compressBlock (knownAt 13)
    (Padding.paddedMessage patternedInput) 832 = knownAt 14 := by
  change Ripemd160.compressBlock H13
    (Padding.paddedMessage patternedInput) 832 = H14
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H13 _ _ 832 (by
    rw [patternedInput_size]; omega),
    compress13 H13, PatternedDigestD.step13]

theorem step14 : Ripemd160.compressBlock (knownAt 14)
    (Padding.paddedMessage patternedInput) 896 = knownAt 15 := by
  change Ripemd160.compressBlock H14
    (Padding.paddedMessage patternedInput) 896 = H15
  rw [paddedMessage_split,
    HashSpecBridge.compressBlock_append_left H14 _ _ 896 (by
    rw [patternedInput_size]; omega),
    compress14 H14, PatternedDigestD.step14]

theorem step15 : Ripemd160.compressBlock (knownAt 15)
    (Padding.paddedMessage patternedInput) 960 = knownAt 16 := by
  change Ripemd160.compressBlock H15
    (Padding.paddedMessage patternedInput) 960 = H16
  rw [HashSpecBridge.paddedMessage_eq_prefix_tail]
  have hprefix : (HashSpecBridge.fullPrefix patternedInput).size = 960 := by
    simp [patternedInput_size]
  have hright := HashSpecBridge.compressBlock_append_right H15
    (HashSpecBridge.fullPrefix patternedInput)
    (HashSpecBridge.canonicalTail patternedInput) 0
  rw [hprefix] at hright
  norm_num at hright
  rw [hright, canonicalTail_patterned, compress_final, PatternedDigestD.step15]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps
