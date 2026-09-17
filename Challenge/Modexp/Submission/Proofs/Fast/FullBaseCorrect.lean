import Challenge.Modexp.Submission.Proofs.Bytecode.FullBaseHitTrace
import Challenge.Modexp.Submission.Proofs.Fast.FullBaseValueBridge
import Challenge.Modexp.Submission.Proofs.Fast.Exp
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectCorrect

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 16000000

/-!
# Full-width-base dispatcher closure

This module restores the public `handled_of_baseHead` boundary after pc1639
was redirected. A miss reuses the relocated legacy Horner proof; a hit copies
the exact full-width base, converts it with RR as the reduced first operand,
and rejoins the exponent tail while retaining the raw base in ACC.
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
    (hact : 89 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hb : bsize ≤ 1024) (hb0 : 1 ≤ bsize)
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
    (hr1 : Model.FastRepresents mem 1024 n (Limbs.radix ^ n % mm))
    (hcc : Model.FastRepresents mem 1280 n (Limbs.radix * Limbs.radix ^ n % mm))
    (hrrb : Model.FastRepresents mem 1536 n rr)
    (hacc : Model.FastRepresents mem 256 n 0)
    (hone : Model.FastRepresents mem 768 n 0)
    (hmiss : ¬ FullBase.Matches mem n bsize) :
    ∃ final : State,
      Nonempty (Challenge.EvmProof.GasSteps
        (baseHead s mem n bsize esize msize) final) ∧
        final.isDone = true ∧
        final.toResult = .returned (Challenge.Modexp.spec input) := by
  have hmpos : 0 < mm := lt_of_lt_of_le Limbs.radix_pos hradix
  have hcop : Nat.Coprime (Limbs.radix ^ n) mm :=
    Model.coprime_radix_pow_of_odd hodd n
  have hbword : bsize < 2 ^ 256 :=
    lt_of_le_of_lt hb (by norm_num)
  have hredirect : Challenge.EvmProof.GasSteps
      (baseHead s mem n bsize esize msize)
      (FullBase.entryState s mem n bsize esize msize) :=
    Challenge.EvmProof.GasSteps.cast
      (Bytecode.FullBaseHitTrace.gasSteps_redirect s mem n bsize esize msize
        hcode hfork hrun hnp) rfl rfl
  have hguard := Bytecode.FullBaseHitTrace.gasSteps_guard
    s mem n bsize esize msize hn32 hbword hact hcode hfork hrun hnp
  by_cases hmatch : FullBase.Matches mem n bsize
  · exact False.elim (hmiss hmatch)
  · have hguardMiss : Challenge.EvmProof.GasSteps
        (FullBase.entryState s mem n bsize esize msize)
        (FullBase.fallbackState s mem n bsize esize msize) := by
      simpa [hmatch] using hguard
    obtain ⟨final, ⟨tr⟩, hdone, hres⟩ :=
      handled_of_baseFallback input s mem n bsize esize msize mm minv rr sub spec
        hcode hfork hrun hnp hdata hstack hact hn hn32 hb hb0 he hmz hm32 hbsize
        hesize hmsz hmm hodd hradix hrrlt hrrmod hframe hmod hr1 hcc hrrb hacc hone
        (fun mem' bM hframe' hmod' hbase' hone' hEb' hbMlt' hbMform' hraw' =>
          FixedDirectCorrect.handled_of_entryStateConcrete input s mem'
            n bsize esize msize mm minv bM sub spec hcode hfork hrun hnp hdata
            hstack hact hn hn32 hb he hmz hm32 hbsize hesize hmsz hmm hodd hradix
            hbMlt' hbMform' hframe' hmod' hbase' hone' hEb'
            ⟨_, hraw', Nat.mod_modEq _ _, Nat.mod_lt _ hmpos⟩)
    exact ⟨final, ⟨(hredirect.trans hguardMiss).trans tr⟩, hdone, hres⟩

end Challenge.Modexp.Submission.Proofs.Fast.Exp
