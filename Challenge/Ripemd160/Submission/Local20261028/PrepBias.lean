import Mathlib.Tactic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RawExpressionAC
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PrepBias
open EvmSemantics
 theorem add_sub_self (a b : UInt256) : UInt256.add a (UInt256.sub b a) = b := by
  unfold UInt256.add UInt256.sub
  congr 1
  exact add_sub_cancel a.val b.val
 theorem add_sub_tail (a b c : UInt256) :
    UInt256.add a (UInt256.add (UInt256.sub b a) c) = UInt256.add b c := by
  rw [← RawExpressionAC.add_assoc, add_sub_self]
#print axioms add_sub_tail
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.PrepBias
