import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart38

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

theorem amStep_readWord_disjoint (memory : ByteArray) (pa pb n addr : Nat)
    (_hn : 1 ≤ n) (hdisj : addr + 32 ≤ 8256 ∨ 8256 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (amStep memory pa pb n j).memory addr =
      MachineState.readWord memory addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (amStep memory pa pb n (j + 1)).memory addr =
          MachineState.readWord (amStep memory pa pb n j).memory addr := by
        simp only [amStep]
        exact readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
