import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreCopyJoin
import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreBinding
import Challenge.Ripemd160.Submission.Local20261028.RecArmsDispatch
import Challenge.Ripemd160.Submission.Local20261028.RecPatterned128Entry
import Challenge.Ripemd160.Submission.Local20261028.RecDirectGuardSize
import Challenge.Ripemd160.Submission.Local20261028.RecEntryPrefilter
import Challenge.Ripemd160.Submission.Local20261028.ColdStackCorrect
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreCorrect
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private def initialEnv (input : ByteArray) :
    HoistedStoreSites.Env (initialState Control.submissionBytecode input 0) :=
  ⟨HoistedStoreBinding.inherited_exact, rfl, rfl, deployAddress_not_precompile⟩

private theorem copied_initial (input : ByteArray) (rho : List UInt256) :
    RetainedFallback114.copied (initialState Control.submissionBytecode input 0) rho =
      StackTail.append (Control.PaddingTrace.padCopied input) rho :=
  HoistedStoreCopyJoin.copied_initial input rho

private theorem generic_after_copy (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) (rho : List UInt256) (hcap : rho.length ≤ 20)
    (g : GasSteps (initialState Control.submissionBytecode input 0)
      (RetainedFallback114.copied (initialState Control.submissionBytecode input 0) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState Control.submissionBytecode input gas) (.returned (spec input)) := by
  rw [copied_initial] at g
  exact Control.GenericFramedCorrect.correct input hfit hpos rho hcap
    (g.trans (Control.PaddingTail.gasSteps_push input rho hcap))

/-- Universal correctness for the exact candidate: compact patterned arms behind
the size dispatcher, the window-checked 1000-byte arm, the hoisted `a` arm, the
full pad-only copy, ordinary compressor, and shared-32 path. -/
theorem correct : Correct Control.submissionBytecode := by
  intro input hfit
  by_cases hpass : Control.EntryPrefilter.condition input = 0
  swap
  · exact Control.StackCorrect.correct input hfit
      (Control.EntryPrefilter.positive_of_taken input hpass)
      (Control.EntryPrefilter.gasSteps_taken input hpass)
  have fromGuard : input.size ≠ 1000 →
      GasSteps (initialState Control.submissionBytecode input 0) (Control.DirectGuard.guardEntry input) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState Control.submissionBytecode input gas) (.returned (spec input)) := by
    intro h1000 hguard
    by_cases hallowed : RecognitionAccumulator.Allowed input.size
    · exact Arms.Dispatch.from_entry input hfit hallowed h1000 hguard
    by_cases hempty : input.size = 0
    · exact Control.AbcArm.correct_empty input hfit (TinyGuardLogic.input_eq_empty input hempty)
        (hguard.trans (Arms.Dispatch.gasSteps_to_empty input hempty))
    have harm : GasSteps (initialState Control.submissionBytecode input 0) (Control.AbcArm.armEntry input) :=
      hguard.trans (Control.Patterned128Entry.gasSteps_to_arm input hfit hallowed h1000 hempty)
    by_cases hw : Control.AbcArm.wordCond input = 0
    · have hs4 := Control.AbcArm.size_lt_four_of_wordCond input hfit hw
      exact Control.AbcArm.correct_abc input hfit
        (Control.AbcArm.wordCond_zero_size_pos input hfit (by omega) hs4 hw) harm
    · exact Control.StackCorrect.correct input hfit (by omega)
        (harm.trans ((Control.AbcArm.gasSteps_miss input hw).trans
          (Control.Patterned128Entry.gasSteps_after_arm_miss input hfit hallowed)))
  by_cases h1000 : input.size = 1000
  swap
  · have gs := DataStepper.runLocatedBlock_sound Control.Artifact.submissionArtifact .Osaka
      Control.DirectGuard.sizePath rfl rfl (Control.DirectGuard.run_size_taken input hfit h1000)
      rfl deployAddress_not_precompile
    exact fromGuard h1000 ((Control.EntryPrefilter.gasSteps_fall input hpass).trans gs)
  by_cases href : Low64RepeatMath.condition input = 0
  swap
  · have gs := DataStepper.runLocatedBlock_sound Control.Artifact.submissionArtifact .Osaka
      Control.DirectGuard.sizePath rfl rfl (Control.DirectGuard.run_size_fall input h1000)
      rfl deployAddress_not_precompile
    have ga := HoistedStoreAnchor.taken (initialState Control.submissionBytecode input 0) []
      (initialEnv input) (by decide) href
    exact Arms.Long.correct1000 input hfit h1000
      ((Control.EntryPrefilter.gasSteps_fall input hpass).trans (gs.trans ga))
  by_cases hm : PcSeedRaw.mismatch input = 0
  · rw [HoistedStoreBinding.inherited_exact]
    exact HoistedStoreEntry.eval_success input hpass h1000 href hm
  · let s := initialState Control.submissionBytecode input 0
    have gm := HoistedStoreEntry.miss s [] (initialEnv input) (by decide) rfl rfl
      (Nat.lt_trans hfit (by norm_num)) hpass h1000 href hm
    have g : GasSteps (initialState Control.submissionBytecode input 0)
        (RetainedFallback114.copied s [0]) := by
      simpa only [s, initialState, show UInt256.ofNat 0 = (0 : UInt256) from rfl] using gm
    exact generic_after_copy input hfit (by omega) [0] (by decide) g

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreCorrect
