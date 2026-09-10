import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart33

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem addLimb_spec (x y c : UInt256) (hc : c.toNat ≤ 1) :
    (c + (x + y)).toNat + Limbs.radix *
        (UInt256.lor (UInt256.lt (c + (x + y)) c) (UInt256.lt (x + y) x)).toNat =
      x.toNat + y.toNat + c.toNat ∧
    (UInt256.lor (UInt256.lt (c + (x + y)) c) (UInt256.lt (x + y) x)).toNat ≤ 1 := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hy : y.toNat < 2 ^ 256 := y.val.isLt
  have h1 : (UInt256.lt (c + (x + y)) c).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  have h2 : (UInt256.lt (x + y) x).toNat ≤ 1 := by
    rw [Challenge.EvmProof.Word.word_toNat_lt]
    split <;> omega
  rw [Challenge.EvmProof.Word.word_toNat_lor, or_of_le_one h1 h2]
  simp only [Challenge.EvmProof.Word.word_toNat_lt,
    Challenge.EvmProof.Word.word_toNat_add, Limbs.radix]
  constructor
  · split_ifs <;> omega
  · split_ifs <;> omega

end Challenge.Modexp.Submission.Proofs.Fast.Csub
