import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentHitCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentEntryTrace

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Concrete fixed-exponent route, including every hit and miss. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRouteCorrect

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
open Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRouteLogic
open Challenge.Modexp.Submission.Proofs.Bytecode

private theorem prepend {input : ByteArray} {start middle : State}
    (head : Challenge.EvmProof.GasSteps start middle)
    (suffix : Handled input middle) : Handled input start := by
  rcases suffix with ⟨final, ⟨tail⟩, hdone, hresult⟩
  exact ⟨final, ⟨head.trans tail⟩, hdone, hresult⟩

/-- Instantiate the complete concrete dispatcher contract. -/
def route (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize mm minv bM : Nat)
    (sub : Exp.Subroutines s n bsize mm minv)
    (spec : Exp.SubSpec sub.mpMem sub.amMem n mm (Limbs.radix ^ n) minv)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hactive : 93 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hb : bsize ≤ 256)
    (he : esize ≤ 256) (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize *
      Limbs.radix ^ n [MOD mm])
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 512 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one) :
    Route s memory input n bsize esize msize where
  enter := FixedExponentEntryTrace.gasSteps_entry s memory
    n bsize esize msize hcode hfork hrun hnp
  miss := by
    intro hnot
    by_cases h3 : esize = 3
    · cases h3
      have hv : exponentValue input bsize 3 ≠ 65537 := by
        intro hv
        apply hnot
        exact ⟨16, Case.fermat rfl hv⟩
      exact ((FixedExponentDispatchTrace.gasSteps_entry_three s memory
        n bsize msize hcode hfork hrun hnp).trans
        (FixedExponentValueTrace.gasSteps_check65537_miss s memory input
          n bsize msize hb hv hdata hactive hframe.eoff
          hcode hfork hrun hnp)).trans
        (FixedExponentFallbackTrace.gasSteps_fallback s memory
          n bsize 3 msize hn hn32 hactive hcode hfork hrun hnp)
    · have hentry := FixedExponentDispatchTrace.gasSteps_entry_other
        s memory n bsize esize msize h3 he hcode hfork hrun hnp
      by_cases h1 : esize = 1
      · cases h1
        have hv : exponentValue input bsize 1 ≠ 3 := by
          intro hv
          apply hnot
          exact ⟨1, Case.three rfl hv⟩
        exact (((hentry.trans
          (FixedExponentDispatchTrace.gasSteps_oneWidth_hit s memory
            n bsize msize hcode hfork hrun hnp)).trans
          (FixedExponentValueTrace.gasSteps_checkThree_miss s memory input
            n bsize msize hb hv hdata hactive hframe.eoff
            hcode hfork hrun hnp)).trans
          (FixedExponentFallbackTrace.gasSteps_fallback s memory
            n bsize 1 msize hn hn32 hactive hcode hfork hrun hnp))
      · exact (hentry.trans
          (FixedExponentDispatchTrace.gasSteps_oneWidth_miss s memory
            n bsize esize msize h1 he hcode hfork hrun hnp)).trans
          (FixedExponentFallbackTrace.gasSteps_fallback s memory
            n bsize esize msize hn hn32 hactive hcode hfork hrun hnp)
  hit := by
    rintro ⟨count, hcase⟩
    cases hcase with
    | three hsize hvalue =>
        cases hsize
        have htoSpecial :=
          ((FixedExponentDispatchTrace.gasSteps_entry_other s memory
            n bsize 1 msize (by decide) (by omega) hcode hfork hrun hnp).trans
          (FixedExponentDispatchTrace.gasSteps_oneWidth_hit s memory
            n bsize msize hcode hfork hrun hnp)).trans
          (FixedExponentValueTrace.gasSteps_checkThree_hit s memory input
            n bsize msize hb hvalue hdata hactive hframe.eoff
            hcode hfork hrun hnp)
        have hfixed := FixedExponentHitCorrect.handled_of_fixed input s memory
          n bsize 1 msize mm minv (Limbs.radix ^ n) bM 1 sub spec
          hcode hfork hrun hnp hstack hactive hn hn32 hmz hm32
          hbsize hesize hmsz hmm
          (lt_of_lt_of_le Limbs.radix_pos hradix)
          (Model.coprime_radix_pow_of_odd hodd n) hradix hbMlt hbMform
          (by omega) (by omega)
          (by simpa [exponentValue] using hvalue)
          hframe hmod hbase hone
        exact prepend htoSpecial hfixed
    | fermat hsize hvalue =>
        cases hsize
        have htoSpecial :=
          (FixedExponentDispatchTrace.gasSteps_entry_three s memory
            n bsize msize hcode hfork hrun hnp).trans
          (FixedExponentValueTrace.gasSteps_check65537_hit s memory input
            n bsize msize hb hvalue hdata hactive hframe.eoff
            hcode hfork hrun hnp)
        have hfixed := FixedExponentHitCorrect.handled_of_fixed input s memory
          n bsize 3 msize mm minv (Limbs.radix ^ n) bM 16 sub spec
          hcode hfork hrun hnp hstack hactive hn hn32 hmz hm32
          hbsize hesize hmsz hmm
          (lt_of_lt_of_le Limbs.radix_pos hradix)
          (Model.coprime_radix_pow_of_odd hodd n) hradix hbMlt hbMform
          (by omega) (by omega)
          (by simpa [exponentValue] using hvalue)
          hframe hmod hbase hone
        exact prepend htoSpecial hfixed

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRouteCorrect
