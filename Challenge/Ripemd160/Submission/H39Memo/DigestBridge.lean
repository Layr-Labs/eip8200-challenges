import Challenge.Ripemd160.Submission.H39Memo.InputData
import Challenge.Ripemd160.Spec
import Challenge.Ripemd160.Submission.H39Memo.DigestData
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HashSpecBridge

set_option warningAsError true
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

namespace Challenge.Ripemd160.Submission.H39Memo

open EvmSemantics.Crypto
open Proofs.Bytecode

def zero12 : ByteArray := ByteArray.mk (Array.replicate 12 0)

/-- Lift a finite sequence of certified compression states to the actual specification. -/
theorem spec_of_steps (input expected : ByteArray) (states : Nat → Array UInt32)
    (count : Nat)
    (hcount : Padding.paddedLength input.size / 64 = count)
    (hstart : states 0 = Ripemd160.H0)
    (hstep : ∀ i, i < count →
      Ripemd160.compressBlock (states i) (Padding.paddedMessage input) (i * 64) =
        states (i + 1))
    (hemit : zero12 ++ SpecBridge.emitDigest (states count) = expected) :
    spec input = expected := by
  have habs (i : Nat) (hi : i ≤ count) :
      SpecBridge.absorbBlocks Ripemd160.H0 (Padding.paddedMessage input) 0 i =
        states i := by
    induction i with
    | zero => exact hstart.symm
    | succ i ih =>
        rw [SpecBridge.absorbBlocks_succ, ih (by omega)]
        simpa only [Nat.zero_add] using hstep i (by omega)
  simp only [spec, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, pure_bind,
    List.forIn_pure_yield_eq_foldl, Id.run_pure]
  change zero12 ++ Ripemd160.hash input = expected
  rw [← HashSpecBridge.paddedHash_eq_hash]
  unfold SpecBridge.paddedHash
  rw [hcount, habs count (by omega)]
  exact hemit

end Challenge.Ripemd160.Submission.H39Memo
