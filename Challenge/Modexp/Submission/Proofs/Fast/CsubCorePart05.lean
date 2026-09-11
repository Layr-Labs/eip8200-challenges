import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart04

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

def amStep (memory : ByteArray) (pa pb n : Nat) : Nat → LimbState
  | 0 => ⟨memory, UInt256.ofNat 0⟩
  | j + 1 =>
      let prev := amStep memory pa pb n j
      let x := MachineState.readWord prev.memory (pa + 32 * (n - 1 - j))
      let y := MachineState.readWord prev.memory (pb + 32 * (n - 1 - j))
      let sum := x + y
      let total := prev.flag + sum
      { memory := MachineState.writeBytes prev.memory
          (Data.Bytes.natToBytesPadded total.toNat 32) (8256 + 32 * (n - 1 - j))
        flag := UInt256.lor (UInt256.lt total prev.flag) (UInt256.lt sum x) }

end Challenge.Modexp.Submission.Proofs.Fast.Csub
