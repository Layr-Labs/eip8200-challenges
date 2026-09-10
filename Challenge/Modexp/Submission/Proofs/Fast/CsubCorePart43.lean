import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart42

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

theorem amStep_invariant (memory : ByteArray) (pa pb n : Nat)
    (hn : 1 ≤ n) (hpa : pa + 32 * n ≤ 8256) (hpb : pb + 32 * n ≤ 8256) :
    ∀ j, j ≤ n →
      lowValue (amStep memory pa pb n j).memory 8256 n j +
            (amStep memory pa pb n j).flag.toNat * Limbs.radix ^ j =
          lowValue memory pa n j + lowValue memory pb n j ∧
        (amStep memory pa pb n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [amStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxa : MachineState.readWord (amStep memory pa pb n j).memory
          (pa + 32 * (n - 1 - j)) =
          MachineState.readWord memory (pa + 32 * (n - 1 - j)) :=
        amStep_readWord_disjoint memory pa pb n _ hn (by omega) j (by omega)
      have hxb : MachineState.readWord (amStep memory pa pb n j).memory
          (pb + 32 * (n - 1 - j)) =
          MachineState.readWord memory (pb + 32 * (n - 1 - j)) :=
        amStep_readWord_disjoint memory pa pb n _ hn (by omega) j (by omega)
      have hlimb := addLimb_spec (MachineState.readWord memory (pa + 32 * (n - 1 - j)))
        (MachineState.readWord memory (pb + 32 * (n - 1 - j)))
        (amStep memory pa pb n j).flag ihLe
      rw [lowValue_succ (amStep memory pa pb n (j + 1)).memory 8256 n j,
        amStep_lowValue_stable memory pa pb n j (by omega),
        amStep_readWord_new, amStep_flag_succ,
        lowValue_succ memory pa n j, lowValue_succ memory pb n j, pow_succ]
      simp only [hxa, hxb]
      exact ⟨am_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

end Challenge.Modexp.Submission.Proofs.Fast.Csub
