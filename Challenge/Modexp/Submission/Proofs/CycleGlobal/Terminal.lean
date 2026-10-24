import Challenge.Modexp.Submission.Proofs.CycleGlobal.FourTerminal
import Challenge.Modexp.Submission.Proofs.CycleCaller.Spec
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3Scale
set_option warningAsError true
set_option exponentiation.threshold 4096
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.Terminal
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast

def result (n N A B k : Nat) : Nat :=
  Model.montMul N (Limbs.radix^n) ((fun a => Model.montMul N (Limbs.radix^n) a a)^[k] A) B

noncomputable opaque run (s : State) (mem : ByteArray) (n bsize esize k N A B mi : Nat)
    (hn : n = 4 ∨ n = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem n bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 n N)
    (ha : Model.FastRepresents mem 2112 n A)
    (hb : Model.FastRepresents mem 256 n B)
    (hN : 0 < N) (hodd : N % 2 = 1) (hA : A < N) (hB : B < N) :
    CycleSubmission.Finish.Outcome (FixedDirectStates.special s mem n bsize esize (32*n) k)
      (Precompile.natToBytes (result n N A B k) (32*n)) := by
  by_cases h4 : n = 4
  · subst n
    exact FourTerminal.run s mem bsize esize k N A B mi hk hk16 env hact hcds
      hf hmi hmi1 hinv hmod ha hb hN hodd hA hB
  · have h8 : n = 8 := by omega
    subst n
    exact CallerFixed.run s mem bsize esize k N A B mi hk hk16 env hact hcds
      hf hmi hinv hmod ha hb hN (Nat.odd_iff.mpr hodd) hB

theorem handled {input : ByteArray} {s : State}
    (out : CycleSubmission.Finish.Outcome s (Challenge.Modexp.spec input))
    (hcalls : s.callStack = []) : FixedExponentRoute.Handled input s := by
  refine ⟨out.state, ⟨out.trace⟩, ?_, ?_⟩
  · simp [State.isDone, State.isHalted, State.isRunning, out.halt, out.calls, hcalls]
  · rw [State.toResult_returned _ out.halt, out.bytes]

theorem result_ordinary (n N A B x k : Nat) (hN : 0 < N) (hodd : N % 2 = 1)
    (ha : A ≡ x*Limbs.radix^n [MOD N]) (hb : B ≡ x [MOD N]) :
    result n N A B k = x^(2^k+1)%N := by
  unfold result
  rw [← FixedDirectOutput.fixedDirectValue_eq_iterate]
  exact FixedDirectOutput.directProduct_value hN (Model.coprime_radix_pow_of_odd hodd n) ha hb

theorem result_cube (n N A B x S T : Nat) (hN : 0 < N) (hodd : N % 2 = 1)
    (ha : A ≡ x*S [MOD N]) (hb : B ≡ x*T [MOD N])
    (hscale : S*S*T = Limbs.radix^n * Limbs.radix^n) :
    result n N A B 1 = x^3%N := by
  change Model.montMul N (Limbs.radix^n) (Model.montMul N (Limbs.radix^n) A A) B = _
  exact RootE3Scale.asymmetric_cube hN (Model.coprime_radix_pow_of_odd hodd n) ha hb hscale


/-- Relate the terminal value to the padded MODEXP byte specification. -/
theorem output_eq (input : ByteArray) (n bsize esize msize N value : Nat)
    (hn : 0 < n) (hN : 0 < N)
    (hb : bsize = Challenge.Modexp.baseSize input)
    (he : esize = Challenge.Modexp.exponentSize input)
    (hm : msize = Challenge.Modexp.modulusSize input) (hfull : msize = 32*n)
    (hmod : N = Precompile.bytesToNatPadded input (96+bsize+esize) msize)
    (hv : value = Precompile.bytesToNatPadded input 96 bsize ^
      Precompile.bytesToNatPadded input (96+bsize) esize % N) :
    Precompile.natToBytes value (32*n) = Challenge.Modexp.spec input := by
  unfold Challenge.Modexp.spec
  rw [← hb, ← he, ← hm, if_neg (by omega : msize ≠ 0), ← hmod]
  dsimp only
  rw [Model.modPow_eq_pow_mod hN, ← hv, hfull]

end CycleSubmission.Global.Terminal
