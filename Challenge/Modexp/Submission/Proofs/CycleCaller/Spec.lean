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

/-- MODEXP equality from the actual fixed-exponent caller at PC 2369. The
global dispatcher and conversion proof must still supply these hypotheses. -/
theorem correct_for_input (input : ByteArray) (s : State) (mem : ByteArray)
    (bsize esize k N A B mi : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem 8 bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 8 N)
    (ha : Model.FastRepresents mem 2112 8 A)
    (hb : Model.FastRepresents mem 256 8 B)
    (hN : 0 < N) (hodd : Odd N) (hB : B < N)
    (hencoding : Encodes input N A B k) (hcalls : s.callStack = []) :
    ∃ gas0, ∀ gas, gas0 ≤ gas →
      Eval (withGas (FixedDirectStates.special s mem 8 bsize esize 256 k) gas)
        (.returned (Challenge.Modexp.spec input)) := by
  have out := CallerFixed.run s mem bsize esize k N A B mi hk hk16 env hact hcds
    hf hmi hinv hmod ha hb hN hodd hB
  have h := out.eventually hcalls
  rw [output_eq input N A B k hN hodd hencoding] at h
  exact h

end CycleSubmission.CallerSpec
