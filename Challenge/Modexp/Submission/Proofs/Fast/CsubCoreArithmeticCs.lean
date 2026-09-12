import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreArithmeticAm
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
/-! ## The `CSUB` loop invariant -/

/-- The `CSUB` loop only writes into the `SUBB` block. -/
theorem csStep_readWord_disjoint (memory : ByteArray) (n addr : Nat)
    (_hn : 1 ≤ n) (hdisj : addr + 32 ≤ 1792 ∨ 1792 + 32 * n ≤ addr) :
    ∀ j, j ≤ n → MachineState.readWord (csStep memory n j).memory addr =
      MachineState.readWord memory addr := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
      intro hj
      have hstep : MachineState.readWord (csStep memory n (j + 1)).memory addr =
          MachineState.readWord (csStep memory n j).memory addr := by
        simp only [csStep]
        exact readWord_write_disjoint _ _ _ _ (by omega)
      rw [hstep, ih (by omega)]

theorem csStep_lowValue_stable (memory : ByteArray) (n j : Nat) (hj : j < n) :
    lowValue (csStep memory n (j + 1)).memory 1792 n j =
      lowValue (csStep memory n j).memory 1792 n j := by
  apply lowValue_congr
  intro k hk
  simp only [csStep]
  exact readWord_write_disjoint _ _ _ _ (by omega)

theorem csStep_readWord_new (memory : ByteArray) (n j : Nat) :
    MachineState.readWord (csStep memory n (j + 1)).memory (1792 + 32 * (n - 1 - j)) =
      MachineState.readWord (csStep memory n j).memory (2112 + 32 * (n - 1 - j)) -
        MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)) -
        (csStep memory n j).flag := by
  simp only [csStep]
  exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

theorem csStep_flag_succ (memory : ByteArray) (n j : Nat) :
    (csStep memory n (j + 1)).flag =
      UInt256.lor
        (UInt256.lt (MachineState.readWord (csStep memory n j).memory (2112 + 32 * (n - 1 - j)))
          (MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j))))
        (UInt256.lt
          (MachineState.readWord (csStep memory n j).memory (2112 + 32 * (n - 1 - j)) -
            MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)))
          (csStep memory n j).flag) := by
  simp only [csStep]

/-- The borrow-propagating subtraction invariant:
`Σ_{k<j} d[k] rad^k + Σ_{k<j} m[k] rad^k = Σ_{k<j} t_low[k] rad^k + borrow · rad^j`
with `borrow ∈ {0, 1}`. -/
theorem csStep_invariant (memory : ByteArray) (n : Nat) (hn : 1 ≤ n) (hn32 : n ≤ 8) :
    ∀ j, j ≤ n →
      lowValue (csStep memory n j).memory 1792 n j + lowValue memory 0 n j =
          lowValue memory 2112 n j +
            (csStep memory n j).flag.toNat * Limbs.radix ^ j ∧
        (csStep memory n j).flag.toNat ≤ 1 := by
  intro j
  induction j with
  | zero => intro _; simp [csStep]
  | succ j ih =>
      intro hj
      obtain ⟨ihEq, ihLe⟩ := ih (by omega)
      have hxt : MachineState.readWord (csStep memory n j).memory
          (2112 + 32 * (n - 1 - j)) =
          MachineState.readWord memory (2112 + 32 * (n - 1 - j)) :=
        csStep_readWord_disjoint memory n _ hn (by omega) j (by omega)
      have hxm : MachineState.readWord (csStep memory n j).memory (32 * (n - 1 - j)) =
          MachineState.readWord memory (32 * (n - 1 - j)) :=
        csStep_readWord_disjoint memory n _ hn (by omega) j (by omega)
      have hlimb := subLimb_spec (MachineState.readWord memory (2112 + 32 * (n - 1 - j)))
        (MachineState.readWord memory (32 * (n - 1 - j)))
        (csStep memory n j).flag ihLe
      rw [lowValue_succ (csStep memory n (j + 1)).memory 1792 n j,
        csStep_lowValue_stable memory n j (by omega),
        csStep_readWord_new, csStep_flag_succ,
        lowValue_succ memory 0 n j, lowValue_succ memory 2112 n j, pow_succ]
      simp only [Nat.zero_add, hxt, hxm]
      exact ⟨cs_algebra _ _ _ _ _ _ _ _ _ _ hlimb.1 ihEq, hlimb.2⟩



end Challenge.Modexp.Submission.Proofs.Fast.Csub
