import Challenge.Modexp.Submission.Proofs.CycleCaller.Arithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.Finish
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
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
theorem handled {input : ByteArray} {s : State}
    (out : CycleSubmission.Finish.Outcome s (Challenge.Modexp.spec input))
    (hcalls : s.callStack = []) : FixedExponentRoute.Handled input s := by
  refine ⟨out.state,⟨out.trace⟩,?_,?_⟩
  · simp [State.isDone,State.isHalted,State.isRunning,out.halt,out.calls,hcalls]
  · rw [State.toResult_returned _ out.halt,out.bytes]
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
  rw [← hb,← he,← hm,if_neg (by omega : msize ≠ 0),← hmod]
  dsimp only
  rw [Model.modPow_eq_pow_mod hN,← hv,hfull]
end CycleSubmission.Global.Terminal
