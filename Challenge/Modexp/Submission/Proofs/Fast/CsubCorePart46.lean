import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart45

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

theorem csStep_readWord_new (memory : ByteArray) (n j : Nat) :
    MachineState.readWord (csStep memory n (j + 1)).memory (7168 + 32 * (n - 1 - j)) =
      MachineState.readWord (csStep memory n j).memory (8256 + 32 * (n - 1 - j)) -
        MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)) -
        (csStep memory n j).flag := by
  simp only [csStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

end Challenge.Modexp.Submission.Proofs.Fast.Csub
