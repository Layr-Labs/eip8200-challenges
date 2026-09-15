import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Meter
import Challenge.EvmProof.Word
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
/-!
# Calldata-byte accessor

The compiler inlines the calldata byte read at its single call site (the
one-word base loop reads `CALLDATALOAD`, `PUSH0`, `BYTE` in place).  This
module only names the value such a read produces and the state shape the base
loop continues from; there is no longer an internal jump to certify.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Accessors

open EvmSemantics
open EvmSemantics.EVM

def calldataByteValue (s : State) (offset : UInt256) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord s.executionEnv.calldata offset.toNat)

/-- The state after an inlined byte read: the byte sits on top of `rest` and
execution continues at `returnDest`. -/
def calldataByteReturned (s : State) (offset returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := calldataByteValue s offset :: rest }

end Challenge.Modexp.Submission.Proofs.Bytecode.Accessors
