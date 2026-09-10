import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart47

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

theorem csStep_invariant (memory : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 32) :
    ∀ j, j ≤ n →
      lowValue (csStep memory n j).memory 7168 n j + lowValue memory 0 n j =
          lowValue memory 8256 n j +
            (csStep memory n j).flag.toNat * Limbs.radix ^ j ∧
        (csStep memory n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [csStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (csStep memory n j).memory
          (8256 + 32 * (n - 1 - j)) =
          MachineState.readWord memory (8256 + 32 * (n - 1 - j)) :=
        csStep_readWord_disjoint memory n _ hn (by omega) j (by omega)
      have hxm : MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord memory (32 * (n - 1 - j)) :=
        csStep_readWord_disjoint memory n _ hn (by omega) j (by omega)
      have hlimb := subLimb_spec (MachineState.readWord memory (8256 + 32 * (n - 1 - j)))
        (MachineState.readWord memory (32 * (n - 1 - j)))
        (csStep memory n j).flag ihLe
      rw [lowValue_succ (csStep memory n (j + 1)).memory 7168 n j,
        csStep_lowValue_stable memory n j (by omega),
        csStep_readWord_new, csStep_flag_succ,
        lowValue_succ memory 0 n j, lowValue_succ memory 8256 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨cs_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩

end Challenge.Modexp.Submission.Proofs.Fast.Csub
