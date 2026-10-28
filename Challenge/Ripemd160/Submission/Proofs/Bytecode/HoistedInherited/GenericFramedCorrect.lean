import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.ColdTailCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32TailCorrect

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.GenericFramedCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open HoistedInherited.StaggerPersistentLoopInduction HoistedInherited.PersistentStaggerIteration

/-- The padding remainder, without replaying the prefix that constructs the frame. -/
private noncomputable def gasSteps_pad (input : ByteArray) (hfit : CalldataFits input)
    (hn32 : input.size ≠ 32) (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)
      (StackTail.append (HoistedInherited.PaddingTrace.entryState input) rho) := by
  by_cases hz : input.size % 64 = 0 ∧ input.size < 256
  · rw [HoistedInherited.PaddingTrace.entryState_skip input hz]
    exact HoistedInherited.PaddingTrace.tail_guardSkip input hfit hz rho hcap
  · rw [HoistedInherited.PaddingTrace.entryState_miss input hz]
    exact (HoistedInherited.PaddingTail.gasSteps_guardMiss input hfit hn32 hz rho hcap).trans
      ((HoistedInherited.PaddingTail.gasSteps_setup input hfit rho hcap).trans
        (HoistedInherited.PaddingTail.gasSteps_loop input hfit rho hcap))

section Ordinary
open HoistedInherited.ColdTailCorrect (maskRho)

-- Keep this transition symbolic: some layouts retain a join JUMPDEST and
-- others enter the block directly. Both cases use the existing trace proofs.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
private noncomputable def gasSteps_ordinary (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)
      (loopState input (HoistedInherited.PaddingTrace.entryState input) StackRunBridge.initialHashState StackRunBridge.initialHashState 0
        (DriverTrace.blockCount input) (maskRho rho)) := by
  let s := HoistedInherited.PaddingTrace.entryState input
  let h := StackRunBridge.initialHashState
  have hp0 : ¬ (input.size = 0 * 64 ∧ input.size < 256) := by omega
  have gx : GasSteps (StackTail.append s rho)
      (loopState input s h h 0 (DriverTrace.blockCount input) (maskRho rho)) := by
    by_cases hz : input.size % 64 = 0 ∧ input.size < 256
    · dsimp [s]
      rw [HoistedInherited.PaddingTrace.entryState_skip input hz]
      simp only [loopState, loopCont, LoopCompletionControl.blockPC, blockOff,
        LoopCompletionControl.offIndex, if_neg hp0, offsetWord,
        DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Padding.messageOffset,
        Nat.zero_mul, Nat.add_zero]
      rw [LoopCompletionControl.cont_aligned input hz 0 hp0, Nat.mul_zero, Nat.sub_zero]
      first
      | exact GasSteps.refl _
      | exact GasSteps.cast
          (HoistedInherited.StaggerPersistentLoopSites.gasSteps_join s
            (StaggerPersistentFrame.frame h (UInt256.ofNat 1056)
              (UInt256.ofNat input.size) (maskRho rho))
            (by simp only [StaggerPersistentFrame.frame, maskRho, List.length_append,
                  List.length_cons, List.length_nil]; omega)
            (HoistedInherited.PadSkipEntry.entryState_halt input) (HoistedInherited.PadSkipEntry.entryState_code input)
            (HoistedInherited.PadSkipEntry.entryState_fork input) (HoistedInherited.PadSkipEntry.entryState_noPrecompile input))
          (by dsimp [s]; rw [HoistedInherited.PaddingTrace.entryState_skip input hz]; rfl)
          (by dsimp [s]; rw [HoistedInherited.PaddingTrace.entryState_skip input hz]; rfl)
    · dsimp [s]
      rw [HoistedInherited.PaddingTrace.entryState_miss input hz]
      simp only [loopState, loopCont, LoopCompletionControl.blockPC, blockOff,
        LoopCompletionControl.offIndex, if_neg hp0, offsetWord,
        DriverTrace.messageOffsetWord, DriverTrace.blockOffset, Padding.messageOffset,
        Nat.zero_mul, Nat.add_zero]
      rw [LoopCompletionControl.cont_cold input hz 0]
      first
      | exact GasSteps.refl _
      | exact GasSteps.cast
          (HoistedInherited.StaggerPersistentLoopSites.gasSteps_join s
            (StaggerPersistentFrame.frame h (UInt256.ofNat 1056)
              (UInt256.ofNat 222) (maskRho rho))
            (by simp only [StaggerPersistentFrame.frame, maskRho, List.length_append,
                  List.length_cons, List.length_nil]; omega)
            (HoistedInherited.PadSkipEntry.entryState_halt input) (HoistedInherited.PadSkipEntry.entryState_code input)
            (HoistedInherited.PadSkipEntry.entryState_fork input) (HoistedInherited.PadSkipEntry.entryState_noPrecompile input))
          (by dsimp [s]; rw [HoistedInherited.PaddingTrace.entryState_miss input hz]; rfl)
          (by dsimp [s]; rw [HoistedInherited.PaddingTrace.entryState_miss input hz]; rfl)
  have gp := gasSteps_pad input hfit hn32 rho hcap
  exact gp.trans gx

/-- The ordinary hash route retains its arbitrary bounded suffix through every block. -/
private theorem correct_ordinary (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (hn32 : input.size ≠ 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)) :
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
  have go := HoistedInherited.StaggerPersistentSerialize.gasSteps (states input count)
    (blockOff input (count - 1))
    (Word.ofUInt32 (hashes input (count - 1)).h2) (hashes input count) rho
    (by omega) a.running a.code a.fork a.notPrecompile
  have trace := entryPrefix.trans (gs.trans (gb.trans go))
  apply HoistedInherited.Shared32Correct.eval_of_initial_returned input _ trace rfl
  · exact states_callStack input count
  · exact HoistedInherited.StaggerPersistentSerialize.returned_spec_of_hashArray _ input _ _ (maskRho rho) _
      (hashArray_hashes input hfit hpositive count (Nat.le_refl _))

end Ordinary

section Shared32
open HoistedInherited.Shared32Scratch HoistedInherited.Shared32Sites Paired144WordRound HoistedInherited.Shared32Start

private def gasSteps_shared32 (input : ByteArray) (h32 : input.size = 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20) :
    GasSteps (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)
      (atState (tableState input) 824 (bodyFrame ++ rho)) := by
  let s := HoistedInherited.PaddingTrace.padCopied input
  have e : Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have hframe : HoistedInherited.PaddingTrace.initialFrame input ++ rho = entryFrame ++ rho := by rw [entry_frame_eq input h32]
  have hactive : s.activeWords = UInt256.ofNat 34 := copied_active input h32
  have g1 : GasSteps (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)
      (atState s 143 (entryFrame ++ rho)) := by
    have ga := HoistedInherited.Shared32Alignment.gasSteps s e (HoistedInherited.PaddingTrace.initialFrame input ++ rho)
      (by rw [List.length_append, HoistedInherited.PaddingTrace.initialFrame_length]; omega) h32
    simpa only [HoistedInherited.PaddingTrace.padFramed, StackTail.append, hframe, atState, s] using ga
  have g4 := HoistedInherited.Shared32Trace.gasSteps_sparse s e factorPlusWord (UInt256.ofNat 4294967295)
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3)
    (fusedCoefficientWord 0 2)
    (Word.ofUInt32 StackRunBridge.initialHashState.h4) (Word.ofUInt32 StackRunBridge.initialHashState.h3)
    (Word.ofUInt32 StackRunBridge.initialHashState.h2) (Word.ofUInt32 StackRunBridge.initialHashState.h1)
    (Word.ofUInt32 StackRunBridge.initialHashState.h0) (UInt256.ofNat 32) rho (by omega)
    (by rw [HoistedInherited.Shared32Start.copied_memory]; have hh := HoistedInherited.Shared32Scratch.copiedMemory_size input (by omega); omega)
    (by rw [HoistedInherited.Shared32Start.copied_memory]; intro a ha hb; exact HoistedInherited.Shared32Scratch.copiedMemory_zero input a (by omega))
    hactive (by decide) h32 rfl
  have g5 := HoistedInherited.Shared32Trace.gasSteps_table s e factorPlusWord
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3)
    (fusedCoefficientWord 0 2)
    (Word.ofUInt32 StackRunBridge.initialHashState.h4) (Word.ofUInt32 StackRunBridge.initialHashState.h3)
    (Word.ofUInt32 StackRunBridge.initialHashState.h2) (Word.ofUInt32 StackRunBridge.initialHashState.h1)
    (Word.ofUInt32 StackRunBridge.initialHashState.h0) (UInt256.ofNat 9949) rho (by omega) hactive
  have hm : sparseMemory s.memory = PairedScheduleMemory.writeWord s.memory 162 highWord := by
    rw [show s.memory = copiedMemory input from copied_memory input]
    exact copiedMemory_sparse input (by omega)
  rw [hm] at g4
  have g := g1.trans (g4.trans g5)
  simpa only [atState, tableState, s, copied_memory, frame, bodyFrame, maskRho,
    StaggerPersistentFrame.frame, HoistedInherited.Pair13Endian.stk, List.append_assoc, List.cons_append, List.nil_append] using g

private theorem correct_shared32 (input : ByteArray) (h32 : input.size = 32)
    (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let s := HoistedInherited.Shared32Start.tableState input
  have e : HoistedInherited.Shared32Sites.Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have gs := gasSteps_shared32 input h32 rho hcap
  have gc := HoistedInherited.Shared32TailCorrect.gasSteps_core s e input rfl h32 (HoistedInherited.Shared32Start.table_active input) rho hcap
  have trace := entryPrefix.trans (gs.trans gc)
  apply HoistedInherited.Shared32Correct.eval_of_initial_returned input _ trace rfl rfl
  exact HoistedInherited.Shared32Core.returned_spec s input h32 (HoistedInherited.Shared32Start.table_ready input h32)

end Shared32

/-- Any trace reaching the generic padding frame with a bounded stack suffix
can reuse the ordinary or shared-32 hash proof, independently of the entry prefix. -/
theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (hpositive : 0 < input.size) (rho : List UInt256) (hcap : rho.length ≤ 20)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (StackTail.append (HoistedInherited.PaddingTrace.padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases h32 : input.size = 32
  · exact correct_shared32 input h32 rho hcap entryPrefix
  · exact correct_ordinary input hfit hpositive h32 rho hcap entryPrefix

#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.GenericFramedCorrect
