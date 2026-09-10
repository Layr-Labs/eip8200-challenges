import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart41

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

theorem amStep_flag_succ (memory : ByteArray) (pa pb n j : Nat) :
    (amStep memory pa pb n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt ((amStep memory pa pb n j).flag +
          (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (amStep memory pa pb n j).memory (pb + 32 * (n - 1 - j))))
          (amStep memory pa pb n j).flag)
        (UInt256.lt
          (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
            MachineState.readWord (amStep memory pa pb n j).memory (pb + 32 * (n - 1 - j)))
          (MachineState.readWord (amStep memory pa pb n j).memory
            (pa + 32 * (n - 1 - j)))) := by
  simp only [amStep]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
