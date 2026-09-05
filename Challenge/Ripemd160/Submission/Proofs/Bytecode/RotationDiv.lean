import Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationMultiply
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DivShift

set_option warningAsError true

/-!
# The rotation fold with `DIV` in place of `SWAP1; SHR`

`RotationMultiply.rawRot_mul` extracts the rotated word from the factor product
with `SHR`.  Because the caller supplies the shift below the product, that form
needs a `SWAP1` first.  `DIV` pops its numerator first and its denominator
second, which is exactly the order the stack already has, so supplying
`2 ^ (32 - r)` instead of `32 - r` removes the swap without changing the
computed value.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationDiv

open EvmSemantics

/-- The `MUL; DIV` rotation fold agrees with the `MUL; SWAP1; SHR` fold. -/
theorem rawRot_mul_div (q : UInt256) (r : Nat)
    (hq : q.toNat < 2 ^ 32) (hr : r ≤ 32) :
    UInt256.div
      (UInt256.mul (UInt256.ofNat (0x100000001 : Nat)) q)
      (UInt256.ofNat (2 ^ (32 - r))) = StackRound.stackRawRot q r := by
  rw [DivShift.div_two_pow_eq_shiftRight _ (show 32 - r < 256 by omega)]
  exact RotationMultiply.rawRot_mul q r hq hr

end Challenge.Ripemd160.Submission.Proofs.Bytecode.RotationDiv
