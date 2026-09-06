import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestA
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestB
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestC
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestD

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
  rw [hright, canonicalTail_patterned, compress_final]
  simpa [finalWords] using PatternedDigestD.step15

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps
