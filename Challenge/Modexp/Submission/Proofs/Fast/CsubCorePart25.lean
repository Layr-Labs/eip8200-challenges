import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart24

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

def csReturnedState (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest
           memory := MachineState.writeBytes (csStep memory n j).memory
             (MachineState.readPadded (csStep memory n j).memory
               (csSrc memory n j).toNat (32 * n)) pdst.toNat }

end Challenge.Modexp.Submission.Proofs.Fast.Csub
