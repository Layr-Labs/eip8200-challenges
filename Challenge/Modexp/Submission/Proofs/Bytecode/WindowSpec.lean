import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowGuardLogic
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath

set_option warningAsError true

/-!
# Fixed-width window result and MODEXP specification

This is the semantic endpoint for the appended hit trace.  It contains no
artifact facts: the execution layer only has to identify its returned word
with `windowResult`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowSpec

open EvmSemantics
open EvmSemantics.EVM

def baseValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 96 32

def exponentValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 128 32

def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input 160 32

def windowResult (input : ByteArray) : Nat :=
  WindowMath.afterBytes input 128 (modulusValue input) (baseValue input) 32
    (1 % modulusValue input)

theorem windowResult_eq_modPow (input : ByteArray)
    (hmodulus : 0 < modulusValue input) :
    windowResult input =
      Precompile.modPow (baseValue input) (exponentValue input)
        (modulusValue input) := by
  rw [windowResult, WindowMath.afterBytes_one input 128
    (modulusValue input) (baseValue input) 32 hmodulus]
  rw [Algorithm.modPow_eq, if_neg (Nat.ne_of_gt hmodulus)]
  rfl

theorem spec_eq (input : ByteArray) (hmatch : WindowGuardLogic.Matches input)
    (hmodulus : 0 < modulusValue input) :
    spec input = Precompile.natToBytes (windowResult input) 32 := by
  rcases hmatch with ⟨hb, he, hm⟩
  unfold spec
  rw [hb, he, hm]
  rw [if_neg (by norm_num : (32 : Nat) ≠ 0)]
  change Precompile.natToBytes
      (Precompile.modPow (baseValue input) (exponentValue input)
        (modulusValue input)) 32 = _
  rw [← windowResult_eq_modPow input hmodulus]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowSpec
