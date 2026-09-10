import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart23

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

def csSrc (memory : ByteArray) (n j : Nat) : UInt256 :=
  (8256 : UInt256) +
    (115792089237316195423570985008687907853269984665640564039457584007913129638848 : UInt256) *
      csUse memory n j

end Challenge.Modexp.Submission.Proofs.Fast.Csub
