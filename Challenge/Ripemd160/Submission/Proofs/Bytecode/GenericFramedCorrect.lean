import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdTailCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32TailCorrect

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.GenericFramedCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerPersistentLoopInduction PersistentStaggerIteration

/-- The padding remainder, without replaying the prefix that constructs the frame. -/
private noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (PaddingTrace.padFramed input) rho)
      (StackTail.append (PaddingTrace.entryState input) rho) := by
  by_cases hz : input.size % 64 = 0 ∧ input.size < 256
  · rw [PaddingTrace.entryState_skip input hz]
    exact PaddingTrace.tail_guardSkip input hfit hz rho hcap
  · rw [PaddingTrace.entryState_miss input hz]
    exact (PaddingTail.gasSteps_guardMiss input hfit hn32 hz rho hcap).trans
      ((PaddingTail.gasSteps_setup input hfit rho hcap).trans
        (PaddingTail.gasSteps_loop input hfit rho hcap))

section Ordinary
open ColdTailCorrect (maskRho)

-- Keep this transition symbolic: some layouts retain a join JUMPDEST and
-- others enter the block directly. Both cases use the existing trace proofs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private noncomputable def gasSteps_ordinary (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (PaddingTrace.padFramed input) rho)
      (loopState input (PaddingTrace.entryState input) StackRunBridge.initialHashState StackRunBridge.initialHashState 0
        (DriverTrace.blockCount input) (maskRho rho)) := by
  let s := PaddingTrace.entryState input
  let h := StackRunBridge.initialHashState
  have hp0 : ¬ (input.size = 0 * 64 ∧ input.size < 256) := by omega
  have gx : GasSteps (StackTail.append s rho)
      (loopState input s h h 0 (DriverTrace.blockCount input) (maskRho rho)) := by
    by_cases hz : input.size % 64 = 0 ∧ input.size < 256
    · dsimp [s]
      rw [PaddingTrace.entryState_skip input hz]
      simp only [loopState, loopCont, LoopCompletionControl.blockPC, blockOff,
        LoopCompletionControl.offIndex, if_neg hp0, offsetWord,
        DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Padding.messageOffset,
        Nat.zero_mul, Nat.add_zero]
      rw [LoopCompletionControl.cont_aligned input hz 0 hp0, Nat.mul_zero, Nat.sub_zero]
      first
      | exact GasSteps.refl _
      | exact GasSteps.cast
          (StaggerPersistentLoopSites.gasSteps_join s
            (StaggerPersistentFrame.frame h (UInt256.ofNat 1056)
              (UInt256.ofNat input.size) (maskRho rho))
            (by simp only [StaggerPersistentFrame.frame, maskRho, List.length_append,
                  List.length_cons, List.length_nil]; omega)
            (PadSkipEntry.entryState_halt input) (PadSkipEntry.entryState_code input)
            (PadSkipEntry.entryState_fork input) (PadSkipEntry.entryState_noPrecompile input))
          (by dsimp [s]; rw [PaddingTrace.entryState_skip input hz]; rfl)
          (by dsimp [s]; rw [PaddingTrace.entryState_skip input hz]; rfl)
    · dsimp [s]
      rw [PaddingTrace.entryState_miss input hz]
      simp only [loopState, loopCont, LoopCompletionControl.blockPC, blockOff,
        LoopCompletionControl.offIndex, if_neg hp0, offsetWord,
        DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Padding.messageOffset,
        Nat.zero_mul, Nat.add_zero]
      rw [LoopCompletionControl.cont_cold input hz 0]
      first
      | exact GasSteps.refl _
      | exact GasSteps.cast
          (StaggerPersistentLoopSites.gasSteps_join s
            (StaggerPersistentFrame.frame h (UInt256.ofNat 1056)
              (UInt256.ofNat 48) (maskRho rho))
            (by simp only [StaggerPersistentFrame.frame, maskRho, List.length_append,
                  List.length_cons, List.length_nil]; omega)
            (PadSkipEntry.entryState_halt input) (PadSkipEntry.entryState_code input)
            (PadSkipEntry.entryState_fork input) (PadSkipEntry.entryState_noPrecompile input))
          (by dsimp [s]; rw [PaddingTrace.entryState_miss input hz]; rfl)
          (by dsimp [s]; rw [PaddingTrace.entryState_miss input hz]; rfl)
  have gp := gasSteps_pad input hfit hn32 rho hcap
  exact gp.trans gx

/-- The ordinary hash route retains its arbitrary bounded suffix through every block. -/
private theorem correct_ordinary (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (PaddingTrace.padFramed input) rho)) :
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
      GasSteps (loopState input (states input i) (hashes input (i - 1)) (hashes input i) i
        (DriverTrace.blockCount input) (maskRho rho))
        (postState input (states input (i + 1)) (hashes input i) (hashes input (i + 1)) i
          (DriverTrace.blockCount input) (maskRho rho)) := by
    intro i hi
    exact gasSteps_block input hfit hpositive i hi (maskRho rho) hm rho rfl
  have gs := gasSteps_ordinary input hfit hpositive hn32 rho hcap
  have gb := run_blocks input (states input) (hashes input) (maskRho rho) hfit hm hambient
    (fun hc i hi => states_last input hfit hpositive hc i hi) hblock
  let count := DriverTrace.blockCount input
  have a := hambient count (Nat.le_refl _)
  have go := StaggerPersistentSerialize.gasSteps (states input count)
    (blockOff input (count - 1))
    (Word.ofUInt32 (hashes input (count - 1)).h2) (hashes input count) rho
    (by omega) a.running a.code a.fork a.notPrecompile
  have trace := entryPrefix.trans (gs.trans (gb.trans go))
  apply Shared32Correct.eval_of_initial_returned input _ trace rfl
  · exact states_callStack input count
  · exact StaggerPersistentSerialize.returned_spec_of_hashArray _ input _ _ (maskRho rho) _
      (hashArray_hashes input hfit hpositive count (Nat.le_refl _))

end Ordinary

/-- Any trace reaching the generic padding frame with a bounded stack suffix
can reuse the ordinary hash proof when its size is not 32, independently of the entry prefix. -/
theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (PaddingTrace.padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  correct_ordinary input hfit hpositive hn32 rho hcap entryPrefix

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.GenericFramedCorrect
