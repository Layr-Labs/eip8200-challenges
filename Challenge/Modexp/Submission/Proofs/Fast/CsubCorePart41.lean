import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart40

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

theorem amStep_readWord_new (memory : ByteArray) (pa pb n j : Nat) :
    MachineState.readWord (amStep memory pa pb n (j + 1)).memory
        (8256 + 32 * (n - 1 - j)) =
      (amStep memory pa pb n j).flag +
        (MachineState.readWord (amStep memory pa pb n j).memory (pa + 32 * (n - 1 - j)) +
          MachineState.readWord (amStep memory pa pb n j).memory
            (pb + 32 * (n - 1 - j))) := by
  simp only [amStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

end Challenge.Modexp.Submission.Proofs.Fast.Csub
