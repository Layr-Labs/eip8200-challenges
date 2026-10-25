import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Lean.Elab.Tactic.Omega

/- Arithmetic identities for the exact shared-complement dispatch schedule. -/
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.Fast.PredicateIdentity
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Fast

theorem not_parity (x : UInt256) :
    UInt256.isZero (UInt256.land (UInt256.ofNat 1) x) =
      UInt256.land (UInt256.ofNat 1) (UInt256.lnot x) := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hlt : 2 ^ 256 - 1 - x.toNat < 2 ^ 256 := by omega
  have hn : (UInt256.lnot x).toNat = 2 ^ 256 - 1 - x.toNat := by
    simp only [UInt256.lnot, UInt256.size, word_toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt
  have hp : (2 ^ 256 - 1 - x.toNat) % 2 = 1 - x.toNat % 2 := by omega
  have ha : UInt256.land (UInt256.ofNat 1) x = UInt256.ofNat (x.toNat % 2) := by
    conv_lhs => rw [word_eq_ofNat_toNat x]
    exact Exp.land_one x.toNat
  have hb : UInt256.land (UInt256.ofNat 1) (UInt256.lnot x) =
      UInt256.ofNat (1 - x.toNat % 2) := by
    conv_lhs => rw [word_eq_ofNat_toNat (UInt256.lnot x)]
    rw [Exp.land_one, hn, hp]
  rw [ha, hb]
  have hsmall : x.toNat % 2 = 0 ∨ x.toNat % 2 = 1 := by omega
  rcases hsmall with h | h <;> rw [h] <;> decide

theorem max_equality (x : UInt256) :
    UInt256.eq (UInt256.lnot (UInt256.ofNat 0)) x =
      UInt256.isZero (UInt256.lnot x) := by
  have hx : x.toNat < 2 ^ 256 := x.val.isLt
  have hlt : 2 ^ 256 - 1 - x.toNat < 2 ^ 256 := by omega
  have hmax : (UInt256.lnot (UInt256.ofNat 0)).toNat = 2 ^ 256 - 1 := by decide
  have hn : (UInt256.lnot x).toNat = 2 ^ 256 - 1 - x.toNat := by
    simp only [UInt256.lnot, UInt256.size, word_toNat_ofNat]
    exact Nat.mod_eq_of_lt hlt
  unfold UInt256.eq UInt256.isZero
  rw [hmax, hn]
  have heq : 2 ^ 256 - 1 = x.toNat ↔ 2 ^ 256 - 1 - x.toNat = 0 := by omega
  simp only [heq]

theorem same_predicate (x : UInt256) :
    UInt256.lor
      (UInt256.isZero (UInt256.land (UInt256.ofNat 1) x))
      (UInt256.eq (UInt256.lnot (UInt256.ofNat 0)) x) =
    UInt256.lor
      (UInt256.land (UInt256.ofNat 1) (UInt256.lnot x))
      (UInt256.isZero (UInt256.lnot x)) := by
  rw [not_parity, max_equality]

open YulEvmCompiler Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

/-- Orient the shared complemented low bit back to the inherited parity test. -/
theorem complement_parity (x : UInt256) :
    UInt256.land (UInt256.ofNat 1) (UInt256.lnot x) =
      UInt256.isZero (UInt256.land (UInt256.ofNat 1) x) := (not_parity x).symm

/-- Orient the complement test back to the inherited equality predicate. -/
theorem not_isZero (x : UInt256) :
    UInt256.isZero (UInt256.lnot x) =
      UInt256.eq (UInt256.lnot (UInt256.ofNat 0)) x := (max_equality x).symm

end CycleSubmission.Global.Fast.PredicateIdentity
