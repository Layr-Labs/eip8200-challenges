import Challenge.Modexp.Submission.Proofs.CycleGlobal.TailPrefix
noncomputable section
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace CycleSubmission.Global.TailFixed
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast FixedExponentRoute
open CycleSubmission.Global.StackTail
open CycleSubmission CycleSubmission.Global
noncomputable def run8 (s : State) (mem : ByteArray) (n bsize esize k N A B mi : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16)
    (hn : n = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem n bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 n N)
    (ha : Model.FastRepresents mem 2112 n A)
    (hb : Model.FastRepresents mem 256 n B)
    (hN : 0 < N) (hodd : N % 2 = 1) (hB : B < N)
    (hg : (CycleSubmission.CallerPrefix.guardWord mem).toNat ≠ 0) :
    CycleSubmission.Finish.Outcome (append (FixedDirectStates.special s mem n bsize esize (32*n) k) rho)
      (Precompile.natToBytes (Terminal.result n N A B k) (32*n)) := by
  subst n
  exact CycleSubmission.Global.TailRoutes.terminal8 s mem bsize esize k N A B mi rho hrho hk hk16 env hact hcds
    hf hmi hinv hmod ha hb hN (Nat.odd_iff.mpr hodd) hB hg

theorem special (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize k N A B mi : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16)
    (hn : n = 4 ∨ n = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hactLe : s.activeWords.toNat ≤ 289)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hcalls : s.callStack = []) (hdata : s.executionEnv.calldata = input)
    (hvalid : Challenge.Modexp.ValidInput input)
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
    Handled input (append (FixedDirectStates.special s mem n bsize esize msize k) rho) := by
  have hout := Terminal.output_eq input n bsize esize msize N _ (by omega) hN
    hbs hes hms hfull hm hv
  by_cases h4 : n = 4
  · subst n
    rw [hfull]
    exact CycleSubmission.Global.TailFourRoute.handled4 input s mem bsize esize k N A B mi rho hrho hk hk16 env hact hactLe hcds
      hcalls hdata hvalid hf hmi hmi1 hinv hmod ha hb hodd hA hB hout (by omega)
  · have h8 : n = 8 := by omega
    by_cases hg : (CycleSubmission.CallerPrefix.guardWord mem).toNat ≠ 0
    · have out := run8 s mem n bsize esize k N A B mi rho hrho h8 hk hk16 env hact hcds
        hf hmi hinv hmod ha hb hN hodd hB hg
      rw [hout] at out
      rw [← hfull] at out
      exact Terminal.handled out hcalls
    · subst h8
      have hms8 : msize = 256 := by omega
      subst hms8
      have head := CycleSubmission.Global.TailRoutes.bail8 s mem bsize esize k mi rho hrho hk hk16 env hact hcds hf (by omega)
      obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
        (CycleSubmission.CallerPrefix.stateAt s mem k (UInt256.ofNat 2519)
          ((UInt256.ofNat k :: Exp.outer 8 bsize esize 256) ++ rho) 207)
        (env.transfer rfl rfl) rfl
        (by simp [append, CycleSubmission.CallerPrefix.stateAt, CycleSubmission.EntryMeaning.saved,
          CycleSubmission.CallerPrefix.frame, Exp.outer] <;> omega)
        hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
        (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rw [hdata, ← hms]; omega)
      exact ⟨done, ⟨head.trans tail⟩, hd, by
        change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
        simpa only [hdata] using hr⟩

theorem ordinary (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize N A B mi : Nat)
    (rho : List UInt256) (hrho : rho.length ≤ 16)
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
    Handled input (append (FixedExponentRoute.entryState s mem n bsize esize msize) rho) := by
  have bail (tr : GasSteps (append (FixedExponentRoute.entryState s mem n bsize esize msize) rho)
      (append (FixedDirectStates.bailState s mem n bsize esize msize) rho)) :
      Handled input (append (FixedExponentRoute.entryState s mem n bsize esize msize) rho) := by
    obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
      (append (FixedDirectStates.bailState s mem n bsize esize msize) rho) (env.transfer rfl rfl) rfl
      (by simp [append, FixedDirectStates.bailState, FixedDirectStates.outer, Exp.outer] <;> omega)
      hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
      (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rw [hdata, ← hms]; omega)
    refine ⟨done, ⟨tr.trans tail⟩, hd, ?_⟩
    change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
    simpa only [hdata] using hr
  by_cases he3 : esize = 3
  · rcases he3 with rfl
    have entry := CycleSubmission.Global.TailPrefix.gasSteps_entry_three s mem n bsize msize rho hrho
      env.code env.forkEq env.running env.noPrecompile
    by_cases he : Precompile.bytesToNatPadded input (96+bsize) 3 = 65537
    · have hit := CycleSubmission.Global.TailPrefix.gasSteps_check65537_hit s mem input n bsize msize rho hrho
        hbsize he hdata hact hf.eoff env.code env.forkEq env.running env.noPrecompile
      apply FixedRoute.prepend (entry.trans hit)
      apply special input s mem n bsize 3 msize 16 N A B mi rho hrho hn (by decide) (by decide)
        env hact hactLe (by rw [hdata]; exact lt_trans hvalid.1 (by norm_num)) hcalls hdata hvalid
        hf hmi hmi1 hinv hmod ha hb hN hodd hA hB hbs hes hms hfull hm
      rw [he]
      simpa only [show (2:Nat)^16+1=65537 from by decide] using
        (Terminal.result_ordinary n N A B _ 16 hN hodd hAe hBe)
    · exact bail (entry.trans (CycleSubmission.Global.TailPrefix.gasSteps_check65537_miss s mem input
        n bsize msize rho hrho hbsize he hdata hact hf.eoff env.code env.forkEq env.running env.noPrecompile))
  · exact bail ((CycleSubmission.Global.TailPrefix.gasSteps_entry_other s mem n bsize esize msize rho hrho
      he3 hesize env.code env.forkEq env.running env.noPrecompile).trans
      (CycleSubmission.Global.TailPrefix.gasSteps_oneWidth_miss s mem n bsize esize msize rho hrho
        env.code env.forkEq env.running env.noPrecompile))

#print axioms run8
#print axioms special
#print axioms ordinary
end CycleSubmission.Global.TailFixed
