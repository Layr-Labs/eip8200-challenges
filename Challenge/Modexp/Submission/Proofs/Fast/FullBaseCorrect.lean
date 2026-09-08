import Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseValueBridge
import Challenge.Modexp.Submission.Proofs.Fast.RawBaseRestack

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Full-width raw-base dispatcher closure

The base-head redirect enters the width-only raw dispatcher directly. Both
high-top and low-top full-width inputs use the same RR-first Montgomery call.
RR is reduced; the raw second operand need only fit n limbs. Width mismatches
retain the relocated legacy Horner path. The former top-bit helper stays at
its original offsets but is no longer reached from baseHead.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Exp

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

theorem handled_of_baseHead (input : ByteArray) (s : State) (mem : ByteArray)
    (n bsize esize msize mm minv rr : Nat)
    (sub : Subroutines s n bsize mm minv)
    (spec : SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hact : 298 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 32) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
    (he : esize ≤ 1024) (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm)
    (hrrlt : rr < mm)
    (hrrmod : rr ≡ Limbs.radix ^ n * Limbs.radix ^ n [MOD mm])
    (hframe : Frame mem n bsize minv)
    (hmod : Model.FastRepresents mem 0 n mm)
    (hr1 : Model.FastRepresents mem 4096 n (Limbs.radix ^ n % mm))
    (hcc : Model.FastRepresents mem 5120 n (Limbs.radix * Limbs.radix ^ n % mm))
    (hrrb : Model.FastRepresents mem 6144 n rr)
    (hacc : Model.FastRepresents mem 1024 n 0)
    (hone : Model.FastRepresents mem 3072 n 0) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (baseHead s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm :=
    Model.coprime_radix_pow_of_odd hodd n
  have hredirect : Challenge.EvmProof.GasSteps
      (baseHead s mem n bsize esize msize)
      (FullBase.rawDispatchState s mem n bsize esize msize) :=
    Challenge.EvmProof.GasSteps.cast
      (Bytecode.FullBaseHitTrace.gasSteps_redirect s mem n bsize esize msize
        hcode hfork hrun hnp) rfl rfl
  by_cases hraw : bsize = 32 * n
  · have htrace := gasSteps_rawBaseChain s sub input mem esize msize rr hraw
      hdata hn hn32 hact hrrlt hframe hmod hrrb hcode hfork hrun hnp
    have hframeC := rawBaseCopy_frame (input := input) hn32 hframe
    have hframeM := sub.mpFrame 6144 2048 2048 (rawBaseCopy mem input n) (by omega) hframeC
    have hEb : EbInv
        (mcopyMem (sub.mpMem 6144 2048 2048 (rawBaseCopy mem input n)) 1024 4096 (32 * n))
        n mm (Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n % mm)
        (expAcc mm (Limbs.radix ^ n)
          (Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n % mm)
          (expBits input bsize) 0) := by
      simpa only [hraw, expAcc] using
        rawBaseCopy_ebInv spec mem input hn hn32 hmpos hcop hrrmod hrrlt
          hframe.minvW hmod hr1 hrrb hone
    obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_bDone input s (sub.mpMem 6144 2048 2048 (rawBaseCopy mem input n))
        n bsize esize msize mm minv
        (Precompile.bytesToNatPadded input 96 bsize * Limbs.radix ^ n % mm) sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn32 hb he hmz hm32 hbsize hesize hmsz
        hmm hodd hradix (Nat.mod_lt _ hmpos) (Nat.mod_modEq _ _) hframeM hEb
    exact ⟨final, ⟨(hredirect.trans htrace).trans tr⟩, hdone, hres⟩
  · have hwidth := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Bytecode.Artifact.submissionArtifact .Osaka rawGuardBlock
      (s := rawGuard s mem n bsize esize msize) hcode hfork
      (run_rawGuard_miss s mem n bsize esize msize hn32 hb hraw hcode hrun)
      hrun hnp
    obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_baseFallback input s mem n bsize esize msize mm minv rr sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn32 hb hb0 he hmz hm32 hbsize
        hesize hmsz hmm hodd hradix hrrlt hrrmod hframe hmod hr1 hcc hrrb hacc hone
    exact ⟨final, ⟨(hredirect.trans hwidth).trans tr⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.Exp
