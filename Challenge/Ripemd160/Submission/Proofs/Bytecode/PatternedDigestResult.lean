import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestSteps

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestResult

open EvmSemantics.Crypto PatternedDigest PatternedInputData PatternedDigestSteps

private theorem knownStep (i : Nat) (hi : i < 16) :
    Ripemd160.compressBlock (knownAt i)
      (Padding.paddedMessage patternedInput) (i * 64) =
      knownAt (i + 1) := by
  interval_cases i <;>
    first
    | exact step0
    | exact step1
    | exact step2
    | exact step3
    | exact step4
    | exact step5
    | exact step6
    | exact step7
    | exact step8
    | exact step9
    | exact step10
    | exact step11
    | exact step12
    | exact step13
    | exact step14
    | exact step15

theorem hashAfter_patterned (i : Nat) (hi : i ≤ 16) :
    CompressionSeamBridge.hashAfter patternedInput i = knownAt i := by
  unfold CompressionSeamBridge.hashAfter
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [SpecBridge.absorbBlocks_succ, ih (by omega)]
      simpa only [Nat.zero_add] using knownStep i (by omega)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedDigestResult
