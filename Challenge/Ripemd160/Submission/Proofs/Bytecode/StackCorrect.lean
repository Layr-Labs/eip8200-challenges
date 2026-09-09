import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateKernel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixStateTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PrefixStateModel

/-- H8 driver kernel state: empty fast path, checked-prefix H1 hit, then the
generic compressor on the prepared (post-CODECOPY when i = 0) state. -/
def nextState : State → ByteArray → Nat → State := PrefixStateKernel.nextState

theorem nextState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x2e0 ≤ address) :
    StackRunBridge.wordAt (nextState s input i) address =
      StackRunBridge.wordAt s address :=
  PrefixStateKernel.nextState_word_above s input i address haddress

/-- The dispatcher result on a block-0 execution, as a four-way choice. -/
private abbrev dispatchResult (s : State) (input : ByteArray) (i : Nat) : State :=
  if i = 0 ∧ Matched input then
    (if Matched2 input then
      (if Matched3 input then
        (if Matched4 input then PrefixStateMemory.resultState4 (PrefixStateMemory.copied s) input
          else PrefixStateMemory.resultState3 (PrefixStateMemory.copied s) input)
        else PrefixStateMemory.resultState2 (PrefixStateMemory.copied s) input)
      else PrefixStateMemory.resultState (PrefixStateMemory.copied s) input i)
    else DriverTrace.compressEntry (prepared s i) input i

noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hnd : PrefixStateModel.double input = true → 2 ≤ i)
    (hnt : PrefixStateModel.triple input = true → 3 ≤ i)
    (hnq : PrefixStateModel.quadruple input = true → 4 ≤ i) :
    GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned (nextState s input i) input i) := by
  by_cases hempty : input.size = 0
  · have gempty := FastEmptyBlock.gasSteps_empty s input i hempty
      ctx.calldata hcode hfork hrun hnp
    exact GasSteps.cast gempty (by rfl) (by
      simp [nextState, PrefixStateKernel.nextState, hempty,
        DriverTrace.compressReturned, FastEmptyBlock.resultState])
  · have gdispatch := FastEmptyBlock.gasSteps_nonempty s input i hfit
      (Nat.pos_of_ne_zero hempty) ctx.calldata hcode hfork hrun hnp
    by_cases hhit : i = 0 ∧ Matched input
    · rcases hhit with ⟨rfl, hmatch⟩
      have hnot2 : ¬ Matched2 input := by
        intro h2
        by_cases h3 : Matched3 input
        · by_cases h4 : Matched4 input
          · have := hnq ((PrefixStateModel.quadruple_iff input).2 ⟨hmatch, h2, h3, h4⟩)
            omega
          · have := hnt ((PrefixStateModel.triple_iff input).2 ⟨⟨hmatch, h2, h3⟩, h4⟩)
            omega
        · have := hnd ((PrefixStateModel.double_iff input).2 ⟨hmatch, h2, h3⟩)
          omega
      have hif : dispatchResult s input 0 =
          PrefixStateMemory.resultState (PrefixStateMemory.copied s) input 0 := by
        show (if 0 = 0 ∧ Matched input then _ else _) = _
        rw [if_pos ⟨rfl, hmatch⟩, if_neg hnot2]
      exact (gdispatch.trans
        ((PrefixStateTrace.gasSteps_dispatch s input 0 hfit hi ctx.calldata
            hcode hfork hrun hnp).cast (by rfl) hif)).cast (by rfl) (by
          simp [nextState, PrefixStateKernel.nextState, hempty, hmatch,
            DriverTrace.compressReturned, PrefixStateMemory.resultState])
    · have ghelper : GasSteps (FastEmptyBlock.nonemptyEntry s input i)
          (DriverTrace.compressEntry (prepared s i) input i) := by
        have hif : dispatchResult s input i =
            DriverTrace.compressEntry (prepared s i) input i := by
          show (if i = 0 ∧ Matched input then _ else _) = _
          rw [if_neg hhit]
        exact (PrefixStateTrace.gasSteps_dispatch s input i hfit hi ctx.calldata
          hcode hfork hrun hnp).cast (by rfl) hif
      have hcode' : (prepared s i).executionEnv.code = submissionBytecode := by
        rw [PrefixStateModel.prepared_executionEnv]; exact hcode
      have hfork' : (prepared s i).fork = .Osaka := by
        simpa [State.fork] using hfork
      have hrun' : (prepared s i).halt = .Running := by
        rw [PrefixStateModel.prepared_halt]; exact hrun
      have hnp' : Precompile.isPrecompileWithConfig
          (prepared s i).executionEnv.precompileConfig
          (prepared s i).executionEnv.fork
          (prepared s i).executionEnv.codeAddr = false := by
        rw [PrefixStateModel.prepared_executionEnv]; exact hnp
      have gcompress := PairedBlockTrace.gasSteps_compress (prepared s i)
        input i h hfit hi (PrefixStateKernel.preparedContext s input i h ctx)
        hcode' hfork' hrun' hnp'
      exact GasSteps.cast (gdispatch.trans (ghelper.trans gcompress)) (by rfl) (by
        simp [nextState, PrefixStateKernel.nextState, hempty, hhit,
          DriverTrace.compressReturned])

/-- The depth-2 ladder rung: one dispatcher execution consumes blocks 0 and 1. -/
noncomputable def gasSteps_block2 (s : State) (input : ByteArray)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hd : PrefixStateModel.double input = true)
    (ctx : StackRunBridge.BlockContext s input 0 h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input 0)
      (DriverTrace.compressReturned (PrefixStateKernel.nextState2 s input) input 1) := by
  obtain ⟨hmatch, hmatch2, hnot3⟩ := (PrefixStateModel.double_iff input).1 hd
  have hsize := PrefixStateData.size_ge_64_of_words input hmatch.2
  have hpos : 0 < input.size := by omega
  have hi : 0 < DriverTrace.blockCount input := DriverTrace.blockCount_pos input
  have gdispatch := FastEmptyBlock.gasSteps_nonempty s input 0 hfit hpos
    ctx.calldata hcode hfork hrun hnp
  have hif : dispatchResult s input 0 =
      PrefixStateMemory.resultState2 (PrefixStateMemory.copied s) input := by
    show (if 0 = 0 ∧ Matched input then _ else _) = _
    rw [if_pos ⟨rfl, hmatch⟩, if_pos hmatch2, if_neg hnot3]
  exact (gdispatch.trans
    ((PrefixStateTrace.gasSteps_dispatch s input 0 hfit hi ctx.calldata
        hcode hfork hrun hnp).cast (by rfl) hif)).cast (by rfl) (by
      simp [PrefixStateKernel.nextState2, DriverTrace.compressReturned,
        PrefixStateMemory.resultState2])

/-- The depth-3 ladder rung: one dispatcher execution consumes blocks 0, 1 and 2. -/
noncomputable def gasSteps_block3 (s : State) (input : ByteArray)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (ht : PrefixStateModel.triple input = true)
    (ctx : StackRunBridge.BlockContext s input 0 h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input 0)
      (DriverTrace.compressReturned (PrefixStateKernel.nextState3 s input) input 2) := by
  obtain ⟨⟨hmatch, hmatch2, hmatch3⟩, hnot4⟩ := (PrefixStateModel.triple_iff input).1 ht
  have hsize := PrefixStateData.size_ge_64_of_words input hmatch.2
  have hpos : 0 < input.size := by omega
  have hi : 0 < DriverTrace.blockCount input := DriverTrace.blockCount_pos input
  have gdispatch := FastEmptyBlock.gasSteps_nonempty s input 0 hfit hpos
    ctx.calldata hcode hfork hrun hnp
  have hif : dispatchResult s input 0 =
      PrefixStateMemory.resultState3 (PrefixStateMemory.copied s) input := by
    show (if 0 = 0 ∧ Matched input then _ else _) = _
    rw [if_pos ⟨rfl, hmatch⟩, if_pos hmatch2, if_pos hmatch3, if_neg hnot4]
  exact (gdispatch.trans
    ((PrefixStateTrace.gasSteps_dispatch s input 0 hfit hi ctx.calldata
        hcode hfork hrun hnp).cast (by rfl) hif)).cast (by rfl) (by
      simp [PrefixStateKernel.nextState3, DriverTrace.compressReturned,
        PrefixStateMemory.resultState3])

noncomputable def gasSteps_block4 (s : State) (input : ByteArray)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (ht : PrefixStateModel.quadruple input = true)
    (ctx : StackRunBridge.BlockContext s input 0 h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input 0)
      (DriverTrace.compressReturned (PrefixStateFourth.nextState4 s input) input 3) := by
  obtain ⟨hmatch, hmatch2, hmatch3, hmatch4⟩ := (PrefixStateModel.quadruple_iff input).1 ht
  have hsize := PrefixStateData.size_ge_64_of_words input hmatch.2
  have hpos : 0 < input.size := by omega
  have hi : 0 < DriverTrace.blockCount input := DriverTrace.blockCount_pos input
  have gdispatch := FastEmptyBlock.gasSteps_nonempty s input 0 hfit hpos
    ctx.calldata hcode hfork hrun hnp
  have hif : dispatchResult s input 0 =
      PrefixStateMemory.resultState4 (PrefixStateMemory.copied s) input := by
    show (if 0 = 0 ∧ Matched input then _ else _) = _
    rw [if_pos ⟨rfl, hmatch⟩, if_pos hmatch2, if_pos hmatch3, if_pos hmatch4]
  exact (gdispatch.trans
    ((PrefixStateTrace.gasSteps_dispatch s input 0 hfit hi ctx.calldata
        hcode hfork hrun hnp).cast (by rfl) hif)).cast (by rfl) (by
      simp [PrefixStateFourth.nextState4, DriverTrace.compressReturned,
        PrefixStateMemory.resultState4])

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := nextState
  executionEnv := PrefixStateKernel.nextState_executionEnv
  halt := PrefixStateKernel.nextState_halt
  callStack := PrefixStateKernel.nextState_callStack
  wordAbove := nextState_word_above
  hashResult := fun s input i h hfit hi ctx hmodel =>
    PrefixStateKernel.nextState_hash s input i h hfit hi ctx hmodel
  double := PrefixStateModel.double
  triple := PrefixStateModel.triple
  quadruple := PrefixStateModel.quadruple
  gasSteps := gasSteps_block
  nextState2 := PrefixStateKernel.nextState2
  executionEnv2 := PrefixStateKernel.nextState2_executionEnv
  halt2 := PrefixStateKernel.nextState2_halt
  callStack2 := PrefixStateKernel.nextState2_callStack
  wordAbove2 := PrefixStateKernel.nextState2_word_above
  doubleBlocks := PrefixStateKernel.double_blockCount
  hashResult2 := PrefixStateKernel.nextState2_hash
  gasSteps2 := gasSteps_block2
  nextState3 := PrefixStateKernel.nextState3
  executionEnv3 := PrefixStateKernel.nextState3_executionEnv
  halt3 := PrefixStateKernel.nextState3_halt
  callStack3 := PrefixStateKernel.nextState3_callStack
  wordAbove3 := PrefixStateKernel.nextState3_word_above
  tripleBlocks := PrefixStateKernel.triple_blockCount
  hashResult3 := PrefixStateKernel.nextState3_hash
  gasSteps3 := gasSteps_block3
  nextState4 := PrefixStateFourth.nextState4
  executionEnv4 := PrefixStateFourth.nextState4_executionEnv
  halt4 := PrefixStateFourth.nextState4_halt
  callStack4 := PrefixStateFourth.nextState4_callStack
  wordAbove4 := PrefixStateFourth.nextState4_word_above
  quadrupleBlocks := PrefixStateFourth.quadruple_blockCount
  hashResult4 := PrefixStateFourth.nextState4_hash
  gasSteps4 := gasSteps_block4

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x3)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  StackRunBridge.correct_of_block_kernel kernel input hfit entryPrefix

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
