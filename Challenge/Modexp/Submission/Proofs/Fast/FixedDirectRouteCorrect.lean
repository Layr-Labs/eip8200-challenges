import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectHitCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectEntryTrace
-- The recogniser misses bail into `modexpBig`; its cold-path proof and location
-- certificates are pure `Proofs.Bytecode` and do not depend on this subtree.
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUMain
import Challenge.Modexp.Submission.Proofs.Bytecode.BigCUBlocks

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! # Concrete fixed-exponent route, including every hit and miss. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectRouteCorrect

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

/-- The diverted recogniser miss, discharged in `modexpBig`.

`bigC_correct` re-reads the header from calldata and is universal in the incoming
memory and stack, so the frame the fast path built is simply discarded.  `bailState`
and `bigCState` are record updates of `s` touching only `pc`, `stack` and `memory`,
so every environment field and both side conditions are `s`'s definitionally. -/
private def bailHandled (input : ByteArray) (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hdata : s.executionEnv.calldata = input) (hstack : s.callStack = [])
    (hvalid : Challenge.Modexp.ValidInput input)
    (hactLe : s.activeWords.toNat ≤ 289)
    (hpos : 0 < Challenge.Modexp.modulusSize input)
    (h : Challenge.EvmProof.GasSteps
      (entryState s memory n bsize esize msize)
      (FixedDirectStates.bailState s memory n bsize esize msize)) :
    Handled input (entryState s memory n bsize esize msize) := by
  have htramp := FixedDirectFallbackTrace.gasSteps_bail s memory
    n bsize esize msize hcode hfork hrun hnp
  have hcd : (FixedDirectStates.bigCState s memory n bsize esize msize).executionEnv.calldata
      = input := hdata
  have env : WindowTwentyOneBinding.Environment Artifact.submissionArtifact .Osaka
      (FixedDirectStates.bigCState s memory n bsize esize msize) :=
    { sizeBound := by
        change Challenge.Modexp.submissionBytecode.size < 2 ^ 256
        rw [Challenge.Modexp.submissionBytecode_size]
        decide
      code := by
        simpa [FixedDirectStates.bigCState, Artifact.submissionArtifact] using hcode
      forkEq := by simpa [FixedDirectStates.bigCState] using hfork
      running := by simpa [FixedDirectStates.bigCState] using hrun
      noPrecompile := by simpa [FixedDirectStates.bigCState] using hnp }
  obtain ⟨final, ⟨tail⟩, hdone, hres⟩ :=
    BigC.U.bigC_correct BigC.UBlocks.setupBlocks BigC.UBlocks.expBlocks
      BigC.UBlocks.mulBlocks BigC.UBlocks.unsignedBlocks
      (FixedDirectStates.bigCState s memory n bsize esize msize)
      env rfl
      (by simp [FixedDirectStates.bigCState, FixedDirectStates.outer, Exp.outer])
      (show (FixedDirectStates.bigCState s memory n bsize esize msize).activeWords.toNat
        ≤ 289 from hactLe)
      (show (FixedDirectStates.bigCState s memory n bsize esize msize).callStack
        = [] from hstack)
      (by rw [hcd]; exact hvalid)
      (by rw [hcd]; exact hpos)
  exact ⟨final, ⟨(h.trans htramp).trans tail⟩, hdone, by rw [hres, hcd]⟩

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
    (hactive : 89 ≤ s.activeWords.toNat)
    -- `bigC_correct` needs an upper bound on `activeWords` and the `size < 2 ^ 64`
    -- component of `ValidInput`; both are in scope at `ShiftCorrect.handled_of_dispatch`.
    (hvalid : Challenge.Modexp.ValidInput input)
    (hactLe : s.activeWords.toNat ≤ 289)
    (hn : 2 ≤ n) (hn32 : n ≤ 8) (hn48 : n = 4 ∨ n = 8) (hminv1 : minv ≠ 1)
    (hb : bsize ≤ 1024)
    (he : esize ≤ 1024) (hmz : 32 < msize) (hm32 : msize ≤ 32 * n)
    (hfull : msize = 32 * n)
    (hbsize : bsize = Challenge.Modexp.baseSize input)
    (hesize : esize = Challenge.Modexp.exponentSize input)
    (hmsz : msize = Challenge.Modexp.modulusSize input)
    (hmm : mm = Precompile.bytesToNatPadded input (96 + bsize + esize) msize)
    (hodd : mm % 2 = 1) (hradix : Limbs.radix ≤ mm) (hbMlt : bM < mm)
    (hbMform : bM ≡ Precompile.bytesToNatPadded input 96 bsize *
      Limbs.radix ^ n [MOD mm])
    (hframe : Exp.Frame memory n bsize minv)
    (hmod : Model.FastRepresents memory 0 n mm)
    (hbase : Model.FastRepresents memory 2112 n bM)
    (hone : ∃ one, one < Limbs.radix ∧
      Model.FastRepresents memory 768 n one)
    (hraw : ∃ rawBase, Model.FastRepresents memory 256 n rawBase ∧
      rawBase ≡ Precompile.bytesToNatPadded input 96 bsize [MOD mm] ∧ rawBase < mm) :
    Route s memory input n bsize esize msize where
  enter := FixedDirectEntryTrace.gasSteps_entry s memory
    n bsize esize msize hcode hfork hrun hnp
  miss := by
    intro hnot
    by_cases h3 : esize = 3
    · cases h3
      have hv : exponentValue input bsize 3 ≠ 65537 := by
        intro hv
        apply hnot
        exact ⟨16, Case.fermat rfl hv⟩
      exact bailHandled input s memory n bsize 3 msize
        hcode hfork hrun hnp hdata hstack hvalid hactLe (by omega)
        ((FixedDirectDispatchTrace.gasSteps_entry_three s memory
          n bsize msize hcode hfork hrun hnp).trans
          (FixedDirectValueTrace.gasSteps_check65537_miss s memory input
            n bsize msize hb hv hdata hactive hframe.eoff
            hcode hfork hrun hnp))
    · have hentry := FixedDirectDispatchTrace.gasSteps_entry_other
        s memory n bsize esize msize h3 he hcode hfork hrun hnp
      by_cases h1 : esize = 1
      · cases h1
        have hv : exponentValue input bsize 1 ≠ 3 := by
          intro hv
          apply hnot
          exact ⟨1, Case.three rfl hv⟩
        exact bailHandled input s memory n bsize 1 msize
          hcode hfork hrun hnp hdata hstack hvalid hactLe (by omega)
          ((hentry.trans
            (FixedDirectDispatchTrace.gasSteps_oneWidth_hit s memory
              n bsize msize hcode hfork hrun hnp)).trans
            (FixedDirectValueTrace.gasSteps_checkThree_miss s memory input
              n bsize msize hb hv hdata hactive hframe.eoff
              hcode hfork hrun hnp))
      · exact bailHandled input s memory n bsize esize msize
          hcode hfork hrun hnp hdata hstack hvalid hactLe (by omega)
          (hentry.trans
            (FixedDirectDispatchTrace.gasSteps_oneWidth_miss s memory
              n bsize esize msize h1 he hcode hfork hrun hnp))
  hit := by
    rcases hraw with ⟨rawBase, hrawRep, hrawForm, hrawLt⟩
    rintro ⟨count, hcase⟩
    cases hcase with
    | three hsize hvalue =>
        cases hsize
        have htoSpecial :=
          ((FixedDirectDispatchTrace.gasSteps_entry_other s memory
            n bsize 1 msize (by decide) (by omega) hcode hfork hrun hnp).trans
          (FixedDirectDispatchTrace.gasSteps_oneWidth_hit s memory
            n bsize msize hcode hfork hrun hnp)).trans
          (FixedDirectValueTrace.gasSteps_checkThree_hit s memory input
            n bsize msize hb hvalue hdata hactive hframe.eoff
            hcode hfork hrun hnp)
        have hfixed := FixedDirectHitCorrect.handled_of_fixed input s memory
          n bsize 1 msize mm minv bM
          rawBase 1 sub spec
          hcode hfork hrun hnp hstack hactive hn hn32 hn48 hminv1 hmz hm32 hfull
          hbsize hesize hmsz hmm
          (lt_of_lt_of_le Limbs.radix_pos hradix)
          (Model.coprime_radix_pow_of_odd hodd n) hradix hbMlt hbMform
          hrawForm
          (by omega) (by omega)
          (by simpa [exponentValue] using hvalue)
          hframe hmod hbase hrawRep hrawLt hone
        exact prepend htoSpecial hfixed
    | fermat hsize hvalue =>
        cases hsize
        have htoSpecial :=
          (FixedDirectDispatchTrace.gasSteps_entry_three s memory
            n bsize msize hcode hfork hrun hnp).trans
          (FixedDirectValueTrace.gasSteps_check65537_hit s memory input
            n bsize msize hb hvalue hdata hactive hframe.eoff
            hcode hfork hrun hnp)
        have hfixed := FixedDirectHitCorrect.handled_of_fixed input s memory
          n bsize 3 msize mm minv bM
          rawBase 16 sub spec
          hcode hfork hrun hnp hstack hactive hn hn32 hn48 hminv1 hmz hm32 hfull
          hbsize hesize hmsz hmm
          (lt_of_lt_of_le Limbs.radix_pos hradix)
          (Model.coprime_radix_pow_of_odd hodd n) hradix hbMlt hbMform
          hrawForm
          (by omega) (by omega)
          (by simpa [exponentValue] using hvalue)
          hframe hmod hbase hrawRep hrawLt hone
        exact prepend htoSpecial hfixed

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectRouteCorrect
