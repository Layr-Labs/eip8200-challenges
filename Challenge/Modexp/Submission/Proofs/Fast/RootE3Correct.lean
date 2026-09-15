import Challenge.Modexp.Submission.Proofs.Fast.RootE3Trace
import Challenge.Modexp.Submission.Proofs.Fast.RootE3Entry
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectCorrect
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace RootE3Correct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open RootE3Phase

def Eligible (input : ByteArray) (n bsize esize : Nat) : Prop :=
  esize = 1 ∧ Precompile.bytesToNatPadded input (96 + bsize) 1 = 3 ∧ (n = 4 ∨ n = 8)

/-- Complete specification adapter for both shift outcomes. The two explicit trace
premises are supplied by the separately proved prefix/loop/phase/tail composition. -/
theorem handled_of_shift_hit (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 89 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hm : 0 < mm)
    (hframe : Exp.Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hone : Model.FastRepresents mem 768 n 0)
    (hmatch : FullBase.Matches mem n bsize)
    (ordinaryTrace : ¬ Eligible input n bsize esize → Challenge.EvmProof.GasSteps
      (Shift.dispState s mem n bsize esize msize)
      (FixedExponentRoute.entryState s (ordinaryOutput mem input n mm) n bsize esize msize))
    (e3Trace : Eligible input n bsize esize → Challenge.EvmProof.GasSteps
      (Shift.dispState s mem n bsize esize msize)
      (FixedExponentRoute.entryState s (e3Output mem input n mm (n / 4)) n bsize esize msize)) :
    FixedExponentRoute.Handled input (Shift.dispState s mem n bsize esize msize) := by
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
      hn hn8 hm hodd hframe hmod hmatch.2 hone
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
    exact FixedDirectCorrect.prepend tr
      (RootE3Hit.handled_of_entry_asymmetric_three input s (e3Output mem input n mm k)
        n bsize msize mm minv X Y (Limbs.radix ^ (3 * k)) (Limbs.radix ^ (2 * k))
        sub spec hcode hfork hrun hnp hdata hb hstack hact hn hn8 hmz hm32
        hbsize hesize hmsz hmm hm (Model.coprime_radix_pow_of_odd hodd n) hradix
        (Nat.mod_lt _ hm) hxform hyform hscale hexp hf hmrep hx hy (Nat.mod_lt _ hm) ⟨0, Limbs.radix_pos, ho⟩)
  · let final := ordinaryOutput mem input n mm
    let base := Precompile.bytesToNatPadded input 96 (32 * n)
    let baseM := base % mm * Limbs.radix ^ n % mm
    have facts := ordinary_output_facts mem input n bsize mm minv
      hn hn8 hm hodd hframe hmod hmatch.2 hone
    rcases facts with ⟨hf, hmrep, hbRep, haRep, ho, hr1⟩
    have hEb : Exp.EbInv (Exp.mcopyMem final 256 1024 (32 * n)) n mm baseM
        (Exp.expAcc mm (Limbs.radix ^ n) baseM (Exp.expBits input bsize) 0) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact Csub.fastRepresents_mcopy_disjoint _ 1024 256 (32 * n) 0 n mm (by omega) hmrep
      · exact Csub.fastRepresents_mcopy _ 1024 256 n (Limbs.radix ^ n % mm) (by omega) hr1
      · exact Csub.fastRepresents_mcopy_disjoint _ 1024 256 (32 * n) 512 n baseM (by omega) hbRep
      · exact ⟨0, Limbs.radix_pos,
          Csub.fastRepresents_mcopy_disjoint _ 1024 256 (32 * n) 768 n 0 (by omega) ho⟩
    have hbForm : baseM ≡ Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n [MOD mm] := by
      rw [hbEq]
      exact (Nat.mod_modEq _ mm).trans ((Nat.mod_modEq base mm).mul_right _)
    have hrawForm : base ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm] := by
      rw [hbEq]
    exact FixedDirectCorrect.prepend (ordinaryTrace hE3)
      (FixedDirectCorrect.handled_of_entryStateConcrete input s final
        n bsize esize msize mm minv baseM sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn8 hb he hmz hm32
        hbsize hesize hmsz hmm hodd hradix (Nat.mod_lt _ hm) hbForm
        hf hmrep hbRep ⟨0, Limbs.radix_pos, ho⟩ hEb ⟨base % mm, haRep, (Nat.mod_modEq base mm).trans hrawForm, Nat.mod_lt _ hm⟩)

#print axioms handled_of_shift_hit
end RootE3Correct

namespace RootE3Correct
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open RootE3Phase

theorem handled_of_bound_shift_hit (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 89 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn8 : n ≤ 8) (hb : bsize ≤ 1024) (he : esize ≤ 1024)
    (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hm : 0 < mm)
    (hframe : Exp.Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hone : Model.FastRepresents mem 768 n 0)
    (hmatch : FullBase.Matches mem n bsize)
    (bindings : RootE3Trace.TraceBindings s mem input n bsize esize msize) :
    FixedExponentRoute.Handled input (Shift.dispState s mem n bsize esize msize) := by
  let e : Shift.Env s := ⟨hcode, hfork, hrun, hnp, hact⟩
  apply handled_of_shift_hit input s mem n bsize esize msize mm minv sub spec
    hcode hfork hrun hnp hdata hstack hact hn hn8 hb he hmz hm32 hbsize hesize hmsz
    hmm hodd hradix hm hframe hmod hone hmatch
  · intro h
    exact RootE3Trace.ordinaryTrace s mem input n bsize esize msize mm minv bindings
      hn hn8 e hm hodd hframe hmod hmatch.2 h
  · intro h
    have hn4 : n = 4 * (n / 4) := by rcases h.2.2 with h4 | h8 <;> omega
    exact RootE3Trace.e3Trace s mem input n bsize esize msize mm minv (n / 4) bindings
      hn hn8 hn4 e hm hodd hframe hmod hmatch.2 h

#print axioms handled_of_bound_shift_hit
end RootE3Correct
