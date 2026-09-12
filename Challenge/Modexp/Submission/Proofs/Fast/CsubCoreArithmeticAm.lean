import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreArithmeticLow
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
/-- The carry-propagating addition invariant:
`Σ_{k<j} a[k] rad^k + Σ_{k<j} b[k] rad^k = Σ_{k<j} t[k] rad^k + carry · rad^j`
with `carry ∈ {0, 1}`. -/
theorem amStep_invariant (memory : ByteArray) (pa pb n : Nat)
    (hn : 1 ≤ n) (hpa : pa + 32 * n ≤ 2112) (hpb : pb + 32 * n ≤ 2112) :
    ∀ j, j ≤ n →
      lowValue (amStep memory pa pb n j).memory 2112 n j +
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
      rw [lowValue_succ (amStep memory pa pb n (j + 1)).memory 2112 n j,
        amStep_lowValue_stable memory pa pb n j (by omega),
        amStep_readWord_new, amStep_flag_succ,
        lowValue_succ memory pa n j, lowValue_succ memory pb n j, pow_succ]
      simp only [hxa, hxb]
      exact ⟨am_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩


end Challenge.Modexp.Submission.Proofs.Fast.Csub
