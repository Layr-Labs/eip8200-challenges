import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart22

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

def csUse (memory : ByteArray) (n j : Nat) : UInt256 :=
  UInt256.lor (MachineState.readWord (csStep memory n j).memory 8224)
    (UInt256.isZero (csStep memory n j).flag)

end Challenge.Modexp.Submission.Proofs.Fast.Csub
