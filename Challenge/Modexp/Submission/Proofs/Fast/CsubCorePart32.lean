import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart31

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

theorem fastRepresents_lowValue (memory : ByteArray) (ptr n : Nat) :
    Model.FastRepresents memory ptr n (lowValue memory ptr n n) :=
  (Model.fastRepresents_iff_value (lowValue_lt memory ptr n n)).2
    (lowValue_full memory ptr n).symm

end Challenge.Modexp.Submission.Proofs.Fast.Csub
