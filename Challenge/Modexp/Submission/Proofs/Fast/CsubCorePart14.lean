import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart13

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

def csEntryState (s : State) (memory : ByteArray) (pdst ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 2139
           stack := [pdst, ret] ++ rest
           memory := memory }

end Challenge.Modexp.Submission.Proofs.Fast.Csub
