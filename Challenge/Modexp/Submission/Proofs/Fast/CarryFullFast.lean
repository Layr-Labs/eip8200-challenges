import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedFour
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullSpecializedEight
import Challenge.Modexp.Submission.Proofs.Fast.CarryFullBase
import Challenge.Modexp.Submission.Proofs.Fast.CarryEntryLemmas
import Challenge.Modexp.Submission.Proofs.Fast.GenericReturnAdapter

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# The multiply kernel for eligible widths only (M9 width-chain narrowing, layer W1)

Drop-in module: copy to `Challenge/Modexp/Submission/Proofs/Fast/CarryFullFast.lean` (checked here as
`M9Width.CarryFullFast`; only the module name differs).  It is the
`CarryFullToCsub` / `CarryFullMonproCsub` / `CarryFullMonproFinal` chain with the
`¬ eligible` branch removed: every statement is the tree's own statement plus ONE hypothesis
`he : StagedOperand.eligible mem n` (resp. `mem (p + 2)`), and the proofs are the eligible
branch of the originals verbatim.  It imports neither `CarryFullFallback` nor the fallback
family of `Cios2Dispatch` nor the trace layer of `Monpro`; once `ExpSubs` uses it
(layer W2), `SquareFull`, `CarryFullFallback`, `CarryFullToCsub`, `CarryFullMonproCsub`,
`CarryFullMonproFinal`, `CarryFullCsub`, `CarryFull` and the Monpro trace layer are
unreferenced from the live proof.

## Definitions assumed (imports only; signatures as they stand in the tree)

* `CarryFull.gasSteps_specializedFour / gasSteps_specializedEight (L : RowLemmas)
    (E : EntryLemmas) s mem pa pb pdst ret rest hcap hrun hcode hfork hnp hact hpa hpaFit hpb
    hpbFit hcds hs32 htl hml (hminv : inverseInvariant mem 4|8)
    (hguard : readWord mem 2720 ≠ ofNat 1) : GasSteps (dispatchState s mem pa pb pdst ret rest)
    (mpCsubState s (rowsCarry (mpZeroed s (stage mem pa n) n) pa pb n n) pdst ret rest)`
  (CarryFullSpecializedFour/Eight.lean)
* `CarryFull.readWord_selected_preserved` (CarryFullBase.lean), `CarryFull.rowLemmas`
  (CarryRowLemmas.lean), `CarryFull.entryLemmas` (CarryEntryLemmas.lean)
* `StagedOperand.eligible mem n := (n = 4 ∨ n = 8) ∧ readWord mem 2720 ≠ ofNat 1`,
  `inputMemory`, `eligible_zeroed`, `eligible_inputMemory`, `fastRepresents_inputMemory`,
  `read_inputMemory_outside` (StagedOperandMemory.lean)
* `CarryResult.selectedRows` (`if eligible mem n then rowsCarry … else rowsMem …`),
  `selectedRows_agree` (CarryResult.lean); `CarryScratchAgreement.readWord_eq`
* `Monpro.mpZeroed`, `Monpro.mpCsubState`, `Monpro.monpro_tn_le_one` (Monpro.lean, MODEL layer:
  `monpro_tn_le_one` is proved from `rows_invariant`; if the trace cut removes it, use
  `StagedMonpro.monpro_tn_le_one`, whose `hpaFit` is the weaker `… ∨ 2368 ≤ pa`)
* `Cios2Dispatch.dispatchState` (Cios2Dispatch.lean, survives the fallback-family cut)
* `Csub.gasSteps_csub`, `Csub.csStep_readWord_disjoint`, `Csub.csReturnedState`
* `CiosCachedMidMemory.inverseInvariant`

Exactly the tree's module options (`maxRecDepth 40000`, `maxHeartbeats 4000000`); no placeholder proofs,
no axiom declaration, no `native_decide`.
-/

noncomputable section

namespace Challenge.Modexp.Submission.Proofs.Fast.CarryFull

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Dispatch
open CiosCached CiosCachedMidMemory CarryIface
open CarryRowModel CarryResult StagedOperand
open TnM128RowSteps

def retainedFrameFast (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst : UInt256) : List UInt256 :=
  TnM128InitialMultiply.retainedFrame s (stage mem pa n) pa pb n
    (MachineState.readWord mem 2784) (MachineState.readWord mem 2720)
    (MachineState.readWord mem (32*n-32)) (UInt256.ofNat (pa+32*n-32))
    (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32) pdst
    (UInt256.ofNat GenericReturnAdapter.genericShimPC) []

theorem genericShim_jumpDest : Decode.isValidJumpDest
    Challenge.Modexp.submissionBytecode
    (UInt256.ofNat GenericReturnAdapter.genericShimPC).toNat = true := by
  change Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5477 = true
  exact Artifact.isValidJumpDest_index 4392 (by rfl)

theorem retainedFrameFast_length (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst : UInt256) :
    (retainedFrameFast s mem pa pb n pdst).length = 16 := by
  simp [retainedFrameFast, TnM128InitialMultiply.retainedFrame,
    TnCacheFrameOps.frame]

/-- `gasSteps_toCsub` restricted to eligible widths: `mul entry` → the four- or eight-limb rows →
the `CSUB` entry.  The `¬ eligible` branch (the generic `MONPRO` fallback) is gone. -/
opaque gasSteps_toCsubFast (E : EntryLemmas) (s : State) (mem : ByteArray)
    (pa pb n : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 991) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n)
    (he : eligible mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (mpCsubState s (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) pdst
        (UInt256.ofNat GenericReturnAdapter.genericShimPC)
        (retainedFrameFast s mem pa pb n pdst ++ ret :: rest)) := by
  have hprepared : eligible (mpZeroed s (inputMemory mem pa n) n) n :=
    (eligible_zeroed s _ n hn32).2 ((eligible_inputMemory mem pa n).2 he)
  rw [selectedRows, if_pos hprepared, inputMemory, if_pos he]
  by_cases hn4 : n = 4
  · subst n
    simpa [retainedFrameFast, TnM128InitialMultiply.retainedFrame,
      TnCacheFrameOps.frame] using
      (gasSteps_specializedFour E s mem pa pb pdst ret rest hcap hrun hcode
        hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv he.2)
  · have hn8 : n = 8 := he.1.resolve_left hn4
    subst n
    simpa [retainedFrameFast, TnM128InitialMultiply.retainedFrame,
      TnCacheFrameOps.frame] using
      (gasSteps_specializedEight E s mem pa pb pdst ret rest hcap hrun hcode
        hfork hnp hact hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv he.2)

/-- `gasSteps_monproCsub` for eligible widths: through the rows and the final subtraction. -/
opaque gasSteps_monproCsubFast (E : EntryLemmas) (s : State) (mem : ByteArray)
    (pa pb n : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 991) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * n))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * n - 32))
    (hminv : inverseInvariant mem n)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * n ≤ 2816)
    (htn : (MachineState.readWord (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) 2080).toNat
      ≤ 1)
    (he : eligible mem n) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n n pdst
        (UInt256.ofNat GenericReturnAdapter.genericShimPC)
        (retainedFrameFast s mem pa pb n pdst ++ ret :: rest)) := by
  have hto := gasSteps_toCsubFast E s mem pa pb n pdst ret rest hcap hrun hcode hfork hnp hact
      hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hminv he
  have hsuffix :
      (retainedFrameFast s mem pa pb n pdst ++ ret :: rest).length ≤ 1008 := by
    rw [List.length_append, retainedFrameFast_length]
    simp
    omega
  have hcsub := Csub.gasSteps_csub s
      (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n pdst
      (UInt256.ofNat GenericReturnAdapter.genericShimPC)
      (retainedFrameFast s mem pa pb n pdst ++ ret :: rest)
      hsuffix hcode hfork hrun hnp hact hn hn32 genericShim_jumpDest
      ((readWord_selected_preserved s mem pa pb n n 2752 hn32 (by omega)).trans hml)
      ((readWord_selected_preserved s mem pa pb n n 2784 hn32 (by omega)).trans htl)
      ((Csub.csStep_readWord_disjoint
          (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n 2688
            (by omega) (Or.inr (by omega)) n (Nat.le_refl n)).trans
        ((readWord_selected_preserved s mem pa pb n n 2688 hn32 (by omega)).trans hs32))
      hdstFit
      (by
        rw [Csub.csStep_readWord_disjoint
          (selectedRows (mpZeroed s (inputMemory mem pa n) n) pa pb n n) n
          2080 (by omega) (Or.inr (by omega)) n (Nat.le_refl n)]
        exact htn) he.1
  simpa only [mpCsubState, Csub.csEntryState] using hto.trans hcsub

/-- `gasSteps_monproFullOf` for eligible widths. -/
opaque gasSteps_monproFullOfFast (E : EntryLemmas) (s : State) (mem : ByteArray)
    (pa pb p : Nat) (a b mm : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 991) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 2816)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0)
    (he : eligible mem (p + 2)) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (selectedRows (mpZeroed s (inputMemory mem pa (p+2)) (p + 2)) pa pb (p + 2) (p + 2))
        (p + 2) (p + 2) pdst ret rest) := by
  let prepared := inputMemory mem pa (p+2)
  let selected := selectedRows (mpZeroed s prepared (p+2)) pa pb (p+2) (p+2)
  have ha' : Model.FastRepresents prepared pa (p+2) a :=
    (fastRepresents_inputMemory mem pa (p+2) pa (p+2) a hpaFit).2 ha
  have hb' : Model.FastRepresents prepared pb (p+2) b :=
    (fastRepresents_inputMemory mem pa (p+2) pb (p+2) b hpbFit).2 hb
  have hm' : Model.FastRepresents prepared 0 (p+2) mm :=
    (fastRepresents_inputMemory mem pa (p+2) 0 (p+2) mm (by omega)).2 hm
  have hminv' : ((MachineState.readWord prepared (32*(p+2)-32)).toNat *
      (MachineState.readWord prepared 2720).toNat + 1) % 2^256 = 0 := by
    simpa only [prepared,
      read_inputMemory_outside mem pa (p+2) (32*(p+2)-32) (Or.inl (by omega)),
      read_inputMemory_outside mem pa (p+2) 2720 (Or.inr (by decide))] using hminv
  have hr := selectedRows_agree (mpZeroed s prepared (p+2)) pa pb (p+2) (p+2)
    hpaFit hpbFit (by omega) hn32 (by omega)
  have htn' : (MachineState.readWord selected 2080).toNat ≤ 1 := by
    rw [CarryScratchAgreement.readWord_eq hr 2080 (Or.inr (by decide))]
    exact Monpro.monpro_tn_le_one s prepared pa pb p a b mm hn32 hpaFit hpbFit ha' hb' hm' ham
      hmpos hminv'
  have hc := gasSteps_monproCsubFast E s mem pa pb (p+2) pdst ret rest hcap hrun hcode hfork hnp
    hact (by omega) hn32 hpa (by omega) hpb (by omega) hcds hs32 htl hml hminv hjump hdstFit htn' he
  have hshape :
      Csub.csReturnedState s selected (p+2) (p+2) pdst
          (UInt256.ofNat GenericReturnAdapter.genericShimPC)
          (retainedFrameFast s mem pa pb (p+2) pdst ++ ret :: rest) =
        GenericReturnAdapter.returnInput s
          (Csub.csResultMemory selected (p+2) pdst.toNat)
          (TnCacheRowPointers.pointer pb (p+2) (p+2)) (UInt256.ofNat 3543)
          (UInt256.ofNat (pb-32)) (UInt256.ofNat (l1PC (p+2)))
          (TnCacheRowModel.rows
            ⟨mpZeroed s (stage mem pa (p+2)) (p+2), UInt256.ofNat 0⟩ pa pb (p+2) (p+2)).tn
          allOnes
          (MachineState.readWord
            (TnCacheRowModel.rows
              ⟨mpZeroed s (stage mem pa (p+2)) (p+2), UInt256.ofNat 0⟩ pa pb (p+2) (p+2)).memory 128)
          (MachineState.readWord mem 2720)
          (MachineState.readWord mem (32*(p+2)-32))
          (MachineState.readWord mem 2784)
          (MachineState.readWord mem 96) (MachineState.readWord mem 64)
          (MachineState.readWord mem 32)
          (UInt256.ofNat (pa+32*(p+2)-32)) pdst
          (UInt256.ofNat GenericReturnAdapter.genericShimPC) ret rest := by
    rw [Csub.csReturnedState_eq_result]
    simp [retainedFrameFast, TnM128InitialMultiply.retainedFrame,
      TnCacheFrameOps.frame, GenericReturnAdapter.returnInput,
      GenericReturnAdapter.frame16]
  rw [hshape] at hc
  have hret := GenericReturnAdapter.gasSteps_genericReturn s
    (Csub.csResultMemory selected (p+2) pdst.toNat)
    (TnCacheRowPointers.pointer pb (p+2) (p+2)) (UInt256.ofNat 3543)
    (UInt256.ofNat (pb-32)) (UInt256.ofNat (l1PC (p+2)))
    (TnCacheRowModel.rows
      ⟨mpZeroed s (stage mem pa (p+2)) (p+2), UInt256.ofNat 0⟩ pa pb (p+2) (p+2)).tn
    allOnes
    (MachineState.readWord
      (TnCacheRowModel.rows
        ⟨mpZeroed s (stage mem pa (p+2)) (p+2), UInt256.ofNat 0⟩ pa pb (p+2) (p+2)).memory 128)
    (MachineState.readWord mem 2720)
    (MachineState.readWord mem (32*(p+2)-32))
    (MachineState.readWord mem 2784)
    (MachineState.readWord mem 96) (MachineState.readWord mem 64)
    (MachineState.readWord mem 32)
    (UInt256.ofNat (pa+32*(p+2)-32)) pdst
    (UInt256.ofNat GenericReturnAdapter.genericShimPC) ret rest (by omega)
    hrun hcode hfork hnp hjump
  have hretword : UInt256.ofNat ret.toNat = ret :=
    (Challenge.EvmProof.Word.word_eq_ofNat_toNat ret).symm
  have hfinal :
      GenericReturnAdapter.returnOutput s
          (Csub.csResultMemory selected (p+2) pdst.toNat) ret rest =
        Csub.csReturnedState s selected (p+2) (p+2) pdst ret rest := by
    rw [Csub.csReturnedState_eq_result]
    simp [GenericReturnAdapter.returnOutput, GenericReturnAdapter.atState, hretword]
  simpa only [selected, prepared] using hc.trans (hret.cast rfl hfinal)

/-- **The sqCP1m multiply kernel for the surviving widths** (`MonPro(pa, pb) → pdst`): from the
`mul entry` to the return of the final subtraction, four and eight limbs through the kernel
rows.  Statement = `gasSteps_monproFull` + `he`. -/
opaque gasSteps_monproFullFast (s : State) (mem : ByteArray) (pa pb p : Nat)
    (a b mm : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 991) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 88 ≤ s.activeWords.toNat) (hn32 : p + 2 ≤ 8)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * (p + 2) ≤ 2048)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * (p + 2) ≤ 2048)
    (hcds : s.executionEnv.calldata.size < 2 ^ 256)
    (hs32 : MachineState.readWord mem 2688 = UInt256.ofNat (32 * (p + 2)))
    (htl : MachineState.readWord mem 2784 = UInt256.ofNat (2080 + 32 * (p + 2)))
    (hml : MachineState.readWord mem 2752 = UInt256.ofNat (32 * (p + 2) - 32))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hdstFit : pdst.toNat + 32 * (p + 2) ≤ 2816)
    (ha : Model.FastRepresents mem pa (p + 2) a)
    (hb : Model.FastRepresents mem pb (p + 2) b)
    (hm : Model.FastRepresents mem 0 (p + 2) mm)
    (ham : a < mm) (hmpos : 0 < mm)
    (hminv : ((MachineState.readWord mem (32 * (p + 2) - 32)).toNat *
        (MachineState.readWord mem 2720).toNat + 1) % 2 ^ 256 = 0)
    (he : eligible mem (p + 2)) :
    Challenge.EvmProof.GasSteps
      (dispatchState s mem pa pb pdst ret rest)
      (Csub.csReturnedState s
        (selectedRows (mpZeroed s (inputMemory mem pa (p+2)) (p + 2)) pa pb (p + 2) (p + 2))
        (p + 2) (p + 2) pdst ret rest) :=
  gasSteps_monproFullOfFast entryLemmas s mem pa pb p a b mm pdst ret rest hcap hrun hcode
    hfork hnp hact hn32 hpa hpaFit hpb hpbFit hcds hs32 htl hml hjump hdstFit ha hb hm ham hmpos hminv he

end Challenge.Modexp.Submission.Proofs.Fast.CarryFull

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CarryFull.gasSteps_toCsubFast
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CarryFull.gasSteps_monproFullFast
