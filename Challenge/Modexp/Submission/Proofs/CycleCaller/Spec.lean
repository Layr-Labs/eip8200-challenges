import Challenge.Modexp.Submission.Proofs.CycleCaller.Fixed
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace CycleSubmission.CallerSpec
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open CycleSubmission.CallerArithmetic

/-- The two operand encodings established by the existing shift-conversion
proofs: ordinary Montgomery input, or asymmetric input scales for a cube. -/
def Encodes (input : ByteArray) (N A B k : Nat) : Prop :=
  Challenge.Modexp.modulusSize input = 256 ∧
  N = Precompile.bytesToNatPadded input
    (96 + Challenge.Modexp.baseSize input + Challenge.Modexp.exponentSize input) 256 ∧
  let x := Precompile.bytesToNatPadded input 96 (Challenge.Modexp.baseSize input)
  let e := Precompile.bytesToNatPadded input (96 + Challenge.Modexp.baseSize input)
    (Challenge.Modexp.exponentSize input)
  (A ≡ x*R [MOD N] ∧ B ≡ x [MOD N] ∧ e = 2^k+1) ∨
  (k = 1 ∧ e = 3 ∧ ∃ S T, A ≡ x*S [MOD N] ∧ B ≡ x*T [MOD N] ∧ S*S*T = R*R)

theorem output_eq (input : ByteArray) (N A B k : Nat)
    (hN : 0 < N) (hodd : Odd N) (hencoding : Encodes input N A B k) :
    Precompile.natToBytes (CallerTerminal.result N A B k) 256 = Challenge.Modexp.spec input := by
  obtain ⟨hsize, hmod, hcases⟩ := hencoding
  unfold Challenge.Modexp.spec
  rw [hsize]
  simp only [show (256 : Nat) ≠ 0 by decide, if_false]
  rw [← hmod, Model.modPow_eq_pow_mod hN]
  apply congrArg (fun v => Precompile.natToBytes v 256)
  rcases hcases with ⟨ha, hb, he⟩ | ⟨rfl, he, S, T, ha, hb, hs⟩
  · rw [he]
    exact ordinary_power N A B _ k hN hodd ha hb
  · rw [he]
    change Model.montMul N R (Model.montMul N R A A) B = _
    exact asymmetric_cube N A B _ S T hN hodd ha hb hs

end CycleSubmission.CallerSpec
