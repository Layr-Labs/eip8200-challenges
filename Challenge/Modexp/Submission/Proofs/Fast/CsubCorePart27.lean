import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart26

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

def lowValue (memory : ByteArray) (ptr n j : Nat) : Nat :=
  Nat.ofDigits Limbs.radix ((List.range j).map fun k =>
    (MachineState.readWord memory (ptr + 32 * (n - 1 - k))).toNat)

@[simp] theorem lowValue_zero (memory : ByteArray) (ptr n : Nat) :
    lowValue memory ptr n 0 = 0 := by
  simp [lowValue]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
