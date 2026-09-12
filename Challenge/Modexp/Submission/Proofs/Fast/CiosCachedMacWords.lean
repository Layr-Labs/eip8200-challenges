import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames
import Challenge.Modexp.Submission.Proofs.Fast.MacAlt

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def framed (template : State) (pc : UInt256) (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack }

theorem negative32_value : negative32 = UInt256.ofNat (2^256-32) := by decide
theorem allOnes_value : allOnes = maxWord := by decide

def partialCarry (x y c : UInt256) : UInt256 :=
  (UInt256.gt c (x * y + c) -
    (UInt256.lt (UInt256.mulMod y x maxWord) (x * y) -
      UInt256.mulMod y x maxWord)) - x * y

theorem sum_eq (x y t c : UInt256) :
    t + (x * y + c) = macSum x y t c := by
  change UInt256.mk (t.val + ((x * y).val + c.val)) =
    UInt256.mk (c.val + (t.val + (x * y).val))
  congr 1
  ac_rfl

theorem carry_eq (x y t c : UInt256) :
    UInt256.gt (x * y + c) (t + (x * y + c)) + partialCarry x y c =
      macCarry x y t c := by
  simpa only [partialCarry, UInt256.gt, Challenge.EvmProof.Word.word_toNat_add,
    Nat.add_mod_mod, macCarry,
    show (2 : Nat) ^ 256 =
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      from by decide] using MacAlt.macCarryFix x y t c

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
