import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCopyJoin
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreBinding
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Arms.Dispatch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Patterned128Entry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.EntryPrefilter
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.StackCorrect
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCorrect
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

private def initialEnv (input : ByteArray) :
    HoistedStoreSites.Env (initialState HoistedInherited.submissionBytecode input 0) :=
  ⟨HoistedStoreBinding.inherited_exact, rfl, rfl, deployAddress_not_precompile⟩

private theorem copied_initial (input : ByteArray) (rho : List UInt256) :
    RetainedFallback114.copied (initialState HoistedInherited.submissionBytecode input 0) rho =
      StackTail.append (HoistedInherited.PaddingTrace.padCopied input) rho :=
  HoistedStoreCopyJoin.copied_initial input rho

private theorem generic_after_copy (input : ByteArray) (hfit : CalldataFits input)
    (hpos : 0 < input.size) (rho : List UInt256) (hcap : rho.length ≤ 20)
    (g : GasSteps (initialState HoistedInherited.submissionBytecode input 0)
      (RetainedFallback114.copied (initialState HoistedInherited.submissionBytecode input 0) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState HoistedInherited.submissionBytecode input gas) (.returned (spec input)) := by
  rw [copied_initial] at g
  exact HoistedInherited.GenericFramedCorrect.correct input hfit hpos rho hcap
    (g.trans (HoistedInherited.PaddingTail.gasSteps_push input rho hcap))

/-- Universal correctness for the exact candidate: compact patterned arms behind
the size dispatcher, the window-checked 1000-byte arm, the hoisted `a` arm, the
full pad-only copy, ordinary compressor, and shared-32 path. -/
theorem correct : Correct HoistedInherited.submissionBytecode := by
  intro input hfit
  by_cases hpass : HoistedInherited.EntryPrefilter.condition input = 0
  swap
  · exact HoistedInherited.StackCorrect.correct input hfit
      (HoistedInherited.EntryPrefilter.positive_of_taken input hpass)
      (HoistedInherited.EntryPrefilter.gasSteps_taken input hpass)
  have fromGuard : input.size ≠ 1000 →
      GasSteps (initialState HoistedInherited.submissionBytecode input 0) (HoistedInherited.DirectGuard.guardEntry input) →
      ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
        Eval (initialState HoistedInherited.submissionBytecode input gas) (.returned (spec input)) := by
    intro h1000 hguard
    by_cases hallowed : RecognitionAccumulator.Allowed input.size
    · exact Arms.Dispatch.from_entry input hfit hallowed h1000 hguard
    by_cases hempty : input.size = 0
    · exact HoistedInherited.AbcArm.correct_empty input hfit (TinyGuardLogic.input_eq_empty input hempty)
        (hguard.trans (Arms.Dispatch.gasSteps_to_empty input hempty))
    have harm : GasSteps (initialState HoistedInherited.submissionBytecode input 0) (HoistedInherited.AbcArm.armEntry input) :=
      hguard.trans (HoistedInherited.Patterned128Entry.gasSteps_to_arm input hfit hallowed h1000 hempty)
    by_cases hw : HoistedInherited.AbcArm.wordCond input = 0
    · have hs4 := HoistedInherited.AbcArm.size_lt_four_of_wordCond input hfit hw
      exact HoistedInherited.AbcArm.correct_abc input hfit
        (HoistedInherited.AbcArm.wordCond_zero_size_pos input hfit (by omega) hs4 hw) harm
    · exact HoistedInherited.StackCorrect.correct input hfit (by omega)
        (harm.trans ((HoistedInherited.AbcArm.gasSteps_miss input hw).trans
          (HoistedInherited.Patterned128Entry.gasSteps_after_arm_miss input hfit hallowed)))
  by_cases h1000 : input.size = 1000
  swap
  · have gs := DataStepper.runLocatedBlock_sound HoistedInherited.Artifact.submissionArtifact .Osaka
      HoistedInherited.DirectGuard.sizePath rfl rfl (HoistedInherited.DirectGuard.run_size_taken input hfit h1000)
      rfl deployAddress_not_precompile
    exact fromGuard h1000 ((HoistedInherited.EntryPrefilter.gasSteps_fall input hpass).trans gs)
  by_cases href : Low64RepeatMath.condition input = 0
  swap
  · have gs := DataStepper.runLocatedBlock_sound HoistedInherited.Artifact.submissionArtifact .Osaka
      HoistedInherited.DirectGuard.sizePath rfl rfl (HoistedInherited.DirectGuard.run_size_fall input h1000)
      rfl deployAddress_not_precompile
    have ga := HoistedStoreAnchor.taken (initialState HoistedInherited.submissionBytecode input 0) []
      (initialEnv input) (by decide) href
    exact Arms.Long.correct1000 input hfit h1000
      ((HoistedInherited.EntryPrefilter.gasSteps_fall input hpass).trans (gs.trans ga))
  by_cases hm : PcSeedRaw.mismatch input = 0
  · rw [HoistedStoreBinding.inherited_exact]
    exact HoistedStoreEntry.eval_success input hpass h1000 href hm
  · let s := initialState HoistedInherited.submissionBytecode input 0
    have gm := HoistedStoreEntry.miss s [] (initialEnv input) (by decide) rfl rfl
      (Nat.lt_trans hfit (by norm_num)) hpass h1000 href hm
    have g : GasSteps (initialState HoistedInherited.submissionBytecode input 0)
        (RetainedFallback114.copied s [0]) := by
      simpa only [s, initialState, show UInt256.ofNat 0 = (0 : UInt256) from rfl] using gm
    exact generic_after_copy input hfit (by omega) [0] (by decide) g

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreCorrect
