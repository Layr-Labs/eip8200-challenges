import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestSteps
import Mathlib.Tactic.IntervalCases

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestResult

open EvmSemantics.Crypto Patterned376Digest Patterned376InputData Patterned376DigestSteps

private theorem knownStep (i : Nat) (hi : i < 7) :
    Ripemd160.compressBlock (knownAt i)
      (Padding.paddedMessage patterned376Input) (i * 64) =
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

theorem hashAfter_patterned376 (i : Nat) (hi : i ≤ 7) :
    SpecBridge.absorbBlocks Ripemd160.H0
      (Padding.paddedMessage patterned376Input) 0 i = knownAt i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [SpecBridge.absorbBlocks_succ, ih (by omega)]
      simpa only [Nat.zero_add] using knownStep i (by omega)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376DigestResult
