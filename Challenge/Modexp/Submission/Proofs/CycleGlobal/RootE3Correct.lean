import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3Trace
import Challenge.Modexp.Submission.Proofs.CycleGlobal.RootE3Scale
import Challenge.Modexp.Submission.Proofs.CycleGlobal.FixedRoute
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace CycleSubmission.Global.RootE3Correct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open RootE3Phase
open CycleSubmission.Global.Fast

def Eligible (input : ByteArray) (n bsize esize : Nat) : Prop :=
  esize = 1 ∧ Precompile.bytesToNatPadded input (96 + bsize) 1 = 3 ∧ (n = 4 ∨ n = 8)

/-- Complete specification adapter for both shift outcomes. The two explicit trace
premises are supplied by the separately proved prefix/loop/phase/tail composition. -/
theorem handled_of_shift_hit (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (hmi : minv < 2^256)
    (hinv : (mm % Limbs.radix * minv + 1) % 2^256 = 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (_hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (_hradix : Limbs.radix ≤ mm) (hm : 0 < mm)
    (hframe : Exp.Frame mem n bsize 0)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hminvDef : minv = Setup.negWord (Setup.newton8 (mm % Limbs.radix)))
    (hone : Model.FastRepresents mem 768 n 0)
    (hmatch : FullBase.Matches mem n bsize)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hfast : n = 4 ∨ n = 8) (hminv1 : minv ≠ 1)
    -- Threaded straight through to `FixedDirectRouteCorrect.bailHandled`.
    (hvalid : Challenge.Modexp.ValidInput input)
    (hactLe : s.activeWords.toNat ≤ 289)
    (ordinaryTrace : ¬ Eligible input n bsize esize → Challenge.EvmProof.GasSteps
      (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize)
      (FixedExponentRoute.entryState s (ordinaryFinal mem input n mm) n bsize esize msize))
    (e3Trace : Eligible input n bsize esize → Challenge.EvmProof.GasSteps
      (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize)
      (CycleSubmission.Global.Fast.Shift.frameState s (e3Final mem input n mm (n / 4)) 2329 n bsize esize msize)) :
    FixedExponentRoute.Handled input (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize) := by
  have env : Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding.Environment CycleSubmission.Artifact.artifact .Osaka s :=
    ⟨by change CycleSubmission.Artifact.bytecode.size < 2^256; rw [CycleSubmission.Artifact.bytecodeSize]; decide, hcode,hfork,hrun,hnp⟩
  have hcds : s.executionEnv.calldata.size < 2^256 := by rw [hdata]; exact lt_trans hvalid.1 (by norm_num)
  have hbEq : bsize = 32 * n := hmatch.1
  by_cases hE3 : Eligible input n bsize esize
  · have tr := e3Trace hE3
    rcases hE3 with ⟨rfl, hexp, hn48⟩
    let k := n / 4
    have hn4 : n = 4 * k := by rcases hn48 with rfl | rfl <;> decide
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    let X := base % mm * Limbs.radix ^ (3 * k) % mm
    let Y := base % mm * Limbs.radix ^ (2 * k) % mm
    have facts := e3_output_facts mem input n bsize mm minv k
      hn hn8 hm hodd hframe hmod hmatch.2 htn0 hone hminvDef
    rcases facts with ⟨hf, hmrep, hx, hy, ho⟩
    have hxform : X ≡ Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ (3 * k) [MOD mm] := by
      rw [hbEq]
      exact (Nat.mod_modEq _ mm).trans ((Nat.mod_modEq base mm).mul_right _)
    have hyform : Y ≡ Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ (2 * k) [MOD mm] := by
      rw [hbEq]
      exact (Nat.mod_modEq _ mm).trans ((Nat.mod_modEq base mm).mul_right _)
    have hscale : Limbs.radix ^ (3 * k) * Limbs.radix ^ (3 * k) * Limbs.radix ^ (2 * k) =
        Limbs.radix ^ n * Limbs.radix ^ n := by
      conv_rhs => rw [hn4]
      exact RootE3Scale.quarter_scale Limbs.radix k
    -- The shift cleanup tail lands on `e3go` (2471) with the bare outer frame.
    have tr' : Challenge.EvmProof.GasSteps (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize 1 msize)
        (FixedDirectStates.e3go s (e3Final mem input n mm k) n bsize 1 msize) := tr
    have finish := FixedRoute.special input s (e3Final mem input n mm k)
      n bsize 1 msize 1 mm X Y minv hn48 (by decide) (by decide)
      env hact hactLe hcds hstack hdata hvalid hf hmi hminv1 hinv hmrep hx hy hm hodd
      (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) hbsize hesize hmsz hfull hmm
      (by rw [hexp]; exact Terminal.result_cube n mm X Y _ _ _ hm hodd hxform hyform hscale)
    have go := FixedDirectValueTrace.gasSteps_threeHit s (e3Final mem input n mm k)
      n bsize 1 msize hcode hfork hrun hnp
    exact FixedRoute.prepend tr' (FixedRoute.prepend go finish)

  · let final := ordinaryFinal mem input n mm
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    let baseM := base % mm * Limbs.radix ^ n % mm
    have facts := ordinary_output_facts mem input n bsize mm minv
      hn hn8 hm hodd hframe hmod hmatch.2 htn0 hone hminvDef
    rcases facts with ⟨hf, hmrep, hbRep, haRep, ho⟩
    have hbForm : baseM ≡ Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n [MOD mm] := by
      rw [hbEq]
      exact (Nat.mod_modEq _ mm).trans ((Nat.mod_modEq base mm).mul_right _)
    have hrawForm : base ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm] := by
      rw [hbEq]
    exact FixedRoute.prepend (ordinaryTrace hE3)
      (FixedRoute.ordinary input s final n bsize esize msize mm baseM (base%mm) minv
        hfast env hact hactLe hdata hstack hvalid hb he hf hmi hminv1 hinv
        hmrep hbRep haRep hm hodd (Nat.mod_lt _ hm) (Nat.mod_lt _ hm)
        hbsize hesize hmsz hfull hmm hbForm ((Nat.mod_modEq base mm).trans hrawForm))


end CycleSubmission.Global.RootE3Correct

namespace CycleSubmission.Global.RootE3Correct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open RootE3Phase
open CycleSubmission.Global.Fast

theorem handled_of_bound_shift_hit (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (hmi : minv < 2^256)
    (hinv : (mm % Limbs.radix * minv + 1) % 2^256 = 0)
    (hcode : s.executionEnv.code = CycleSubmission.Artifact.bytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 88 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hm : 0 < mm)
    (hframe : Exp.Frame mem n bsize 0)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hminvDef : minv = Setup.negWord (Setup.newton8 (mm % Limbs.radix)))
    (hone : Model.FastRepresents mem 768 n 0)
    (hmatch : FullBase.Matches mem n bsize)
    (htn0 : MachineState.readWord mem 2080 = UInt256.ofNat 0)
    (hfast : n = 4 ∨ n = 8) (hminv1 : minv ≠ 1)
    (hvalid : Challenge.Modexp.ValidInput input)
    (hactLe : s.activeWords.toNat ≤ 289)
    (bindings : RootE3Trace.TraceBindings s mem input n bsize esize msize) :
    FixedExponentRoute.Handled input (CycleSubmission.Global.Fast.Shift.dispState s mem n bsize esize msize) := by
  let e : CycleSubmission.Global.Fast.Shift.Env s := ⟨hcode, hfork, hrun, hnp, hact⟩
  apply handled_of_shift_hit input s mem n bsize esize msize mm minv hmi hinv
    hcode hfork hrun hnp hdata hstack hact hn hn8 hb he hmz hm32 hfull hbsize hesize hmsz
    hmm hodd hradix hm hframe hmod hminvDef hone hmatch htn0 hfast hminv1 hvalid hactLe
  · intro h
    exact RootE3Trace.ordinaryTrace s mem input n bsize esize msize mm minv bindings
      hn hn8 hmatch.1 e hm hodd hframe hmod hminvDef hmatch.2 htn0 h hfast
  · intro h
    have hn4 : n = 4 * (n / 4) := by rcases h.2.2 with h4 | h8 <;> omega
    exact RootE3Trace.e3Trace s mem input n bsize esize msize mm minv (n / 4) bindings
      hn hn8 hmatch.1 hn4 e hm hodd hframe hmod hminvDef hmatch.2 htn0 h

end CycleSubmission.Global.RootE3Correct
