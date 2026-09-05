import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

def headerCheckOrPath := [opAt 919 .OR, opAt 920 .OR]
def headerCheckIsZeroPath := [opAt 921 .ISZERO]
def headerCheckJumpPath := [pushAt 922 2 1234, opAt 923 .JUMPI]

def headerChecksCombinedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1228
    stack := [0, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def headerCheckPassedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 1229
    stack := [1, UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
