import Challenge.Modexp.Submission.Proofs.CycleGlobal.Terminal
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FixedDirectEntryTrace
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Fallback
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace CycleSubmission.Global.FixedRoute
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast
open FixedExponentRoute

theorem prepend {input : ByteArray} {start middle : State}
    (head : GasSteps start middle) (tail : Handled input middle) : Handled input start := by
  obtain ⟨final, ⟨tr⟩, hd, hr⟩ := tail
  exact ⟨final, ⟨head.trans tr⟩, hd, hr⟩

theorem special (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize k N A B mi : Nat)
    (hn : n = 4 ∨ n = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hcalls : s.callStack = [])
    (hf : Exp.Frame mem n bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 n N)
    (ha : Model.FastRepresents mem 2112 n A) (hb : Model.FastRepresents mem 256 n B)
    (hN : 0 < N) (hodd : N % 2 = 1) (hA : A < N) (hB : B < N)
    (hbs : bsize = Challenge.Modexp.baseSize input)
    (hes : esize = Challenge.Modexp.exponentSize input)
    (hms : msize = Challenge.Modexp.modulusSize input) (hfull : msize = 32*n)
    (hm : N = Precompile.bytesToNatPadded input (96+bsize+esize) msize)
    (hv : Terminal.result n N A B k = Precompile.bytesToNatPadded input 96 bsize ^
      Precompile.bytesToNatPadded input (96+bsize) esize % N) :
    Handled input (FixedDirectStates.special s mem n bsize esize msize k) := by
  have out := Terminal.run s mem n bsize esize k N A B mi hn hk hk16 env hact hcds
    hf hmi hmi1 hinv hmod ha hb hN hodd hA hB
  rw [Terminal.output_eq input n bsize esize msize N _ (by omega) hN
    hbs hes hms hfull hm hv] at out
  rw [← hfull] at out
  exact Terminal.handled out hcalls

theorem ordinary (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize N A B mi : Nat)
    (hn : n = 4 ∨ n = 8)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hactLe : s.activeWords.toNat ≤ 289)
    (hdata : s.executionEnv.calldata = input) (hcalls : s.callStack = [])
    (hvalid : Challenge.Modexp.ValidInput input) (hbsize : bsize ≤ 1024) (hesize : esize ≤ 1024)
    (hf : Exp.Frame mem n bsize mi) (hmi : mi < 2^256) (hmi1 : mi ≠ 1)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 n N)
    (ha : Model.FastRepresents mem 2112 n A) (hb : Model.FastRepresents mem 256 n B)
    (hN : 0 < N) (hodd : N % 2 = 1) (hA : A < N) (hB : B < N)
    (hbs : bsize = Challenge.Modexp.baseSize input)
    (hes : esize = Challenge.Modexp.exponentSize input)
    (hms : msize = Challenge.Modexp.modulusSize input) (hfull : msize = 32*n)
    (hm : N = Precompile.bytesToNatPadded input (96+bsize+esize) msize)
    (hAe : A ≡ Precompile.bytesToNatPadded input 96 bsize * Limbs.radix^n [MOD N])
    (hBe : B ≡ Precompile.bytesToNatPadded input 96 bsize [MOD N]) :
    Handled input (FixedExponentRoute.entryState s mem n bsize esize msize) := by
  have bail (tr : GasSteps (FixedExponentRoute.entryState s mem n bsize esize msize)
      (FixedDirectStates.bailState s mem n bsize esize msize)) :
      Handled input (FixedExponentRoute.entryState s mem n bsize esize msize) := by
    obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
      (FixedDirectStates.bailState s mem n bsize esize msize) (env.transfer rfl rfl) rfl
      (by simp [FixedDirectStates.bailState, FixedDirectStates.outer, Exp.outer])
      hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
      (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rw [hdata, ← hms]; omega)
    refine ⟨done, ⟨tr.trans tail⟩, hd, ?_⟩
    change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
    simpa only [hdata] using hr
  by_cases he3 : esize = 3
  · rcases he3 with rfl
    have entry := FixedDirectDispatchTrace.gasSteps_entry_three s mem n bsize msize
      env.code env.forkEq env.running env.noPrecompile
    by_cases he : Precompile.bytesToNatPadded input (96+bsize) 3 = 65537
    · have hit := FixedDirectValueTrace.gasSteps_check65537_hit s mem input n bsize msize
        hbsize he hdata hact hf.eoff env.code env.forkEq env.running env.noPrecompile
      apply prepend (entry.trans hit)
      apply special input s mem n bsize 3 msize 16 N A B mi hn (by decide) (by decide)
        env hact (by rw [hdata]; exact lt_trans hvalid.1 (by norm_num)) hcalls
        hf hmi hmi1 hinv hmod ha hb hN hodd hA hB hbs hes hms hfull hm
      rw [he]
      simpa only [show (2:Nat)^16+1=65537 from by decide] using
        (Terminal.result_ordinary n N A B _ 16 hN hodd hAe hBe)
    · exact bail (entry.trans (FixedDirectValueTrace.gasSteps_check65537_miss s mem input
        n bsize msize hbsize he hdata hact hf.eoff env.code env.forkEq env.running env.noPrecompile))
  · exact bail ((FixedDirectDispatchTrace.gasSteps_entry_other s mem n bsize esize msize
      he3 hesize env.code env.forkEq env.running env.noPrecompile).trans
      (FixedDirectDispatchTrace.gasSteps_oneWidth_miss s mem n bsize esize msize
        env.code env.forkEq env.running env.noPrecompile))

end CycleSubmission.Global.FixedRoute
