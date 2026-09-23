import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTail
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Correct
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTailCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerPersistentLoopInduction PersistentStaggerIteration

def maskRho (rho : List UInt256) : List UInt256 :=
  [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16] ++ rho

noncomputable def gasSteps_start (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (Execution.atPC input 342) rho)
      (loopState input (PaddingTrace.entryState input) StackRunBridge.initialHashState 0
        (DriverTrace.blockCount input) (maskRho rho)) := by
  let s := PaddingTrace.entryState input
  let h := StackRunBridge.initialHashState
  have hr : s.halt = .Running := PadSkipEntry.entryState_halt input
  have hc : s.executionEnv.code = Artifact.submissionArtifact.code := PadSkipEntry.entryState_code input
  have hf : s.fork = .Osaka := PadSkipEntry.entryState_fork input
  have hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := PadSkipEntry.entryState_noPrecompile input
  have hi : s.executionEnv.calldata = input := PadSkipEntry.entryState_calldata input
  have hm : (maskRho rho).length ≤ 880 := by simp only [maskRho, List.length_append, List.length_cons, List.length_nil]; omega
  have gx : GasSteps (StackTail.append s rho)
      {s with pc := UInt256.ofNat 508, stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) (LoopCompletionControl.limit input) (maskRho rho)} := by
    by_cases hz : input.size % 64 = 0
    · have hs : StackTail.append s rho = {s with pc := UInt256.ofNat 508, stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) (UInt256.ofNat input.size) (maskRho rho)} := by
        dsimp [s]
        rw [PaddingTrace.entryState_skip input hz]
        rfl
      exact GasSteps.cast (GasSteps.refl (StackTail.append s rho)) rfl (by
        simpa only [LoopCompletionControl.limit, LoopCompletionControl.limitNat, if_pos hz] using hs)
    · have hs : StackTail.append s rho = {s with pc := UInt256.ofNat 508, stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) (Padding.paddedWord input) (maskRho rho)} := by
        dsimp [s]
        rw [PaddingTrace.entryState_miss input hz]
        rfl
      exact GasSteps.cast (GasSteps.refl (StackTail.append s rho)) rfl (by
        simpa only [LoopCompletionControl.limit, LoopCompletionControl.limitNat, if_neg hz,
          Padding.paddedWord_eq input hfit] using hs)
  have gj := StaggerPersistentLoopSites.gasSteps_join s
    (StaggerPersistentFrame.frame h (UInt256.ofNat 0) (LoopCompletionControl.limit input) (maskRho rho))
    (by simp only [StaggerPersistentFrame.frame, List.length_append, List.length_cons, List.length_nil]; omega)
    hr hc hf hn
  have gp := PaddingTail.gasSteps_pad input hfit hn32 rho hcap
  have g := gp.trans (gx.trans gj)
  simpa only [loopState, LoopCompletionControl.blockPC, Nat.zero_mul,
    if_neg (show input.size ≠ 0 by omega), offsetWord] using g

/-- The ordinary hash route retains its arbitrary bounded suffix through every block. -/
theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32) (hsmall : input.size < 5206)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (Execution.atPC input 342) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  have hm : (maskRho rho).length ≤ 880 := by
    simp only [maskRho, List.length_append, List.length_cons, List.length_nil]
    omega
  have hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient input (states input i) := by
    intro i _
    exact ⟨states_code input i, states_fork input i, states_halt input i,
      states_noPrecompile input i, states_calldata input i⟩
  have hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states input i) (hashes input i) i
        (DriverTrace.blockCount input) (maskRho rho))
        (postState input (states input (i + 1)) (hashes input (i + 1)) i
          (DriverTrace.blockCount input) (maskRho rho)) := by
    intro i hi
    exact ColdOrdinaryBlock.gasSteps (states input i) input i (hashes input i)
      (LoopCompletionControl.limit input) (maskRho rho) hm rho rfl hfit hi
      (states_context input hfit hpositive i (Nat.le_of_lt hi)) (fun _ => hsmall)
      (states_code input i) (states_fork input i) (states_halt input i)
      (states_noPrecompile input i)
  have gs := gasSteps_start input hfit hpositive hn32 rho hcap
  have gb := run_blocks input (states input) (hashes input) (maskRho rho) hfit hm hambient hblock
  let count := DriverTrace.blockCount input
  have a := hambient count (Nat.le_refl _)
  have go := StaggerPersistentSerialize.gasSteps (states input count)
    (limitWord count) (LoopCompletionControl.limit input) (hashes input count) rho
    (by omega) a.running a.code a.fork a.notPrecompile
  have trace := entryPrefix.trans (gs.trans (gb.trans go))
  apply Shared32Correct.eval_of_initial_returned input _ trace rfl
  · exact states_callStack input count
  · exact StaggerPersistentSerialize.returned_spec_of_hashArray _ input _ _ (maskRho rho) _
      (hashArray_hashes input hfit hpositive count (Nat.le_refl _))

#print axioms gasSteps_start
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTailCorrect
