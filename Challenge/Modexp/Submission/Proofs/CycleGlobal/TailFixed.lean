import Challenge.Modexp.Submission.Proofs.CycleGlobal.Fallback
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
open CycleSubmission CycleSubmission.Global
private theorem prepend {input : ByteArray} {start middle : State}
    (head : GasSteps start middle) (tail : Handled input middle) : Handled input start := by
  obtain ⟨final, ⟨tr⟩, hd, hr⟩ := tail
  exact ⟨final, ⟨head.trans tr⟩, hd, hr⟩

noncomputable def run8 (s : State) (mem : ByteArray) (n bsize esize k N A B mi : Nat)
    
    (hn : n = 8) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (env : Environment CycleSubmission.Artifact.artifact .Osaka s)
    (hact : 88 ≤ s.activeWords.toNat) (hcds : s.executionEnv.calldata.size < 2^256)
    (hf : Exp.Frame mem n bsize mi) (hmi : mi < 2^256)
    (hinv : (N % Limbs.radix * mi + 1) % 2^256 = 0)
    (hmod : Model.FastRepresents mem 0 n N)
    (ha : Model.FastRepresents mem 2112 n A)
    (hb : Model.FastRepresents mem 256 n B)
    (hN : 0 < N) (hodd : N % 2 = 1) (hB : B < N)
    (hg : (DirectEightRaw.guardWord mem).toNat ≠ 0) :
    CycleSubmission.Finish.Outcome (SlimFrames.special s mem n bsize esize (32*n) k)
      (Precompile.natToBytes (Terminal.result n N A B k) (32*n)) := by
  subst n
  exact CycleSubmission.Global.TailRoutes.terminal8 s mem bsize esize k N A B mi hk hk16 env hact hcds
    hf hmi hinv hmod ha hb hN (Nat.odd_iff.mpr hodd) hB hg

theorem special (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize k N A B mi : Nat)
    
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
    Handled input (SlimFrames.special s mem n bsize esize msize k) := by
  have hout := Terminal.output_eq input n bsize esize msize N _ (by omega) hN
    hbs hes hms hfull hm hv
  by_cases h4 : n = 4
  · subst n
    rw [hfull]
    exact CycleSubmission.Global.TailFourRoute.handled4 input s mem bsize esize k N A B mi hk hk16 env hact hactLe hcds
      hcalls hdata hvalid hf hmi hmi1 hinv hmod ha hb hodd hA hB hout (by omega)
  · have h8 : n = 8 := by omega
    by_cases hg : (DirectEightRaw.guardWord mem).toNat ≠ 0
    · have out := run8 s mem n bsize esize k N A B mi h8 hk hk16 env hact hcds
        hf hmi hinv hmod ha hb hN hodd hB hg
      rw [hout] at out
      rw [← hfull] at out
      exact Terminal.handled out hcalls
    · subst h8
      have hms8 : msize = 256 := by omega
      subst hms8
      have head := CycleSubmission.Global.TailRoutes.bail8 s mem bsize esize k mi hk hk16 env hact hcds hf (by omega)
      obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
        (DirectEightEntry.bailState s mem bsize esize k)
        (env.transfer rfl rfl) rfl
        (by simp [List.append_nil, DirectEightEntry.bailState, DirectEightRaw.state, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer] <;> omega)
        hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
        (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rw [hdata, ← hms]; omega)
      exact ⟨done, ⟨head.trans tail⟩, hd, by
        change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
        simpa only [hdata] using hr⟩

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
    Handled input (GateRaw.entryState s mem n bsize esize msize) := by
  have hn8 : n ≤ 8 := by omega
  have hf' (sz : Nat) : Exp.Frame (GateScratch.memory mem sz) n bsize mi := GateScratch.frame mem sz n bsize mi hf
  have hmod' (sz : Nat) : Model.FastRepresents (GateScratch.memory mem sz) 0 n N :=
    GateScratch.represents mem sz 0 n N (Or.inl (by omega)) hmod
  have ha' (sz : Nat) : Model.FastRepresents (GateScratch.memory mem sz) 2112 n A :=
    GateScratch.represents mem sz 2112 n A (Or.inr (by decide)) ha
  have hb' (sz : Nat) : Model.FastRepresents (GateScratch.memory mem sz) 256 n B :=
    GateScratch.represents mem sz 256 n B (Or.inl (by omega)) hb
  have bail (tr : GasSteps (GateRaw.entryState s mem n bsize esize msize)
      (SlimFrames.bailState s (GateScratch.memory mem esize) n bsize esize msize)) :
      Handled input (GateRaw.entryState s mem n bsize esize msize) := by
    obtain ⟨done, ⟨tail⟩, hd, hr⟩ := Fallback.correct
      (SlimFrames.bailState s (GateScratch.memory mem esize) n bsize esize msize) (env.transfer rfl rfl) rfl
      (by simp [List.append_nil, SlimFrames.bailState, SlimFrames.guardFrame, SlimFrames.ridingFrame, SlimFrames.frameState, FixedDirectStates.outer, SlimFrames.outer, CycleSubmission.Global.Fast.Shift.entrySlots, CycleSubmission.Global.Fast.Shift.aprevSlot, CycleSubmission.Global.Fast.Shift.hdSlot, Exp.outer] <;> omega)
      hactLe hcalls (by change Challenge.Modexp.ValidInput s.executionEnv.calldata; rwa [hdata])
      (by change 0 < Challenge.Modexp.modulusSize s.executionEnv.calldata; rw [hdata, ← hms]; omega)
    refine ⟨done, ⟨tr.trans tail⟩, hd, ?_⟩
    change done.toResult = .returned (Challenge.Modexp.spec s.executionEnv.calldata) at hr
    simpa only [hdata] using hr
  have hsize : MachineState.readWord s.executionEnv.calldata 32 = UInt256.ofNat esize := by
    rw [hdata, hes]
    rfl
  by_cases he3 : esize = 3
  · rcases he3 with rfl
    by_cases he : Precompile.bytesToNatPadded input (96+bsize) 3 = 65537
    · have hit := GatePrefix.gasSteps_hit s mem input n bsize msize hbsize hact he hdata env hsize hf.eoff
      apply prepend hit
      apply special input s (GateScratch.memory mem 3) n bsize 3 msize 16 N A B mi hn (by decide) (by decide)
        env hact hactLe (by rw [hdata]; exact lt_trans hvalid.1 (by norm_num)) hcalls hdata hvalid
        (hf' 3) hmi hmi1 hinv (hmod' 3) (ha' 3) (hb' 3) hN hodd hA hB hbs hes hms hfull hm
      rw [he]
      simpa only [show (2:Nat)^16+1=65537 from by decide] using
        (Terminal.result_ordinary n N A B _ 16 hN hodd hAe hBe)
    · exact bail (GatePrefix.gasSteps_miss s mem n bsize 3 msize hbsize hact
        (GateRaw.miss_exponent s bsize 3 (GatePrefix.exponent_ne s input bsize he hdata)) env hsize hf.eoff)
  · have hne : UInt256.ofNat esize ≠ UInt256.ofNat 3 := by
      intro h
      have h' := congrArg UInt256.toNat h
      simp only [Word.word_toNat_ofNat] at h'
      have hl : esize < 2^256 := by omega
      rw [Nat.mod_eq_of_lt hl] at h'
      exact he3 (by simpa using h')
    exact bail (GatePrefix.gasSteps_miss s mem n bsize esize msize hbsize hact
      (GateRaw.miss_size s bsize esize hne) env hsize hf.eoff)
#print axioms special
#print axioms ordinary
end CycleSubmission.Global.TailFixed
