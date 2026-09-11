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


noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (_hnd : PrefixStateModel.double input = true → 2 ≤ i) :
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
      have hif : (if 0 = 0 ∧ Matched input then
          PrefixStateMemory.resultState (PrefixStateMemory.copied s) input 0
        else DriverTrace.compressEntry (prepared s 0) input 0) =
        PrefixStateMemory.resultState (PrefixStateMemory.copied s) input 0 := by
        rw [if_pos ⟨rfl, hmatch⟩]
      exact (gdispatch.trans
        ((PrefixStateTrace.gasSteps_dispatch s input 0 hfit hi ctx.calldata
            hcode hfork hrun hnp).cast (by rfl) hif)).cast (by rfl) (by
          simp [nextState, PrefixStateKernel.nextState, hempty, hmatch,
            DriverTrace.compressReturned, PrefixStateMemory.resultState])
    · have ghelper : GasSteps (FastEmptyBlock.nonemptyEntry s input i)
          (DriverTrace.compressEntry (prepared s i) input i) := by
        have hif : (if i = 0 ∧ Matched input then
            PrefixStateMemory.resultState (PrefixStateMemory.copied s) input i
          else DriverTrace.compressEntry (prepared s i) input i) =
          DriverTrace.compressEntry (prepared s i) input i := by
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

/-- The retained two-block interface cannot be selected by this dispatcher. -/
noncomputable def gasSteps_block2 (s : State) (input : ByteArray)
    (h : Compression.HashState) (_hfit : CalldataFits input)
    (hd : PrefixStateModel.double input = true)
    (_ctx : StackRunBridge.BlockContext s input 0 h)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (_hfork : s.fork = .Osaka) (_hrun : s.halt = .Running)
    (_hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input 0)
      (DriverTrace.compressReturned (PrefixStateKernel.nextState2 s input) input 1) := by
  simp [PrefixStateModel.double] at hd

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := nextState
  executionEnv := PrefixStateKernel.nextState_executionEnv
  halt := PrefixStateKernel.nextState_halt
  callStack := PrefixStateKernel.nextState_callStack
  wordAbove := nextState_word_above
  hashResult := fun s input i h hfit hi ctx hmodel =>
    PrefixStateKernel.nextState_hash s input i h hfit hi ctx hmodel
  double := PrefixStateModel.double
  gasSteps := gasSteps_block
  nextState2 := PrefixStateKernel.nextState2
  executionEnv2 := PrefixStateKernel.nextState2_executionEnv
  halt2 := PrefixStateKernel.nextState2_halt
  callStack2 := PrefixStateKernel.nextState2_callStack
  wordAbove2 := PrefixStateKernel.nextState2_word_above
  doubleBlocks := PrefixStateKernel.double_blockCount
  hashResult2 := PrefixStateKernel.nextState2_hash
  gasSteps2 := gasSteps_block2

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x16b)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) :=
  StackRunBridge.correct_of_block_kernel kernel input hfit entryPrefix

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
