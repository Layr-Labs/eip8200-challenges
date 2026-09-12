import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectEmptyReturn

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- Mathematical single-block state shared by the exact compression trace. -/
def nextState (s : State) (input : ByteArray) (i : Nat) : State :=
  PairedBlockModel.resultState s input i

@[simp] theorem nextState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).executionEnv = s.executionEnv := rfl

@[simp] theorem nextState_halt (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).halt = s.halt := rfl

@[simp] theorem nextState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).callStack = s.callStack := rfl

theorem nextState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x400 ≤ address) :
    StackRunBridge.wordAt (nextState s input i) address =
      StackRunBridge.wordAt s address :=
  PairedBlockModel.resultState_word_above s input i address haddress

theorem nextState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (_hfit : CalldataFits input)
    (_hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (_hmodel : CompressionCorrect.hashArray h = CompressionSeamBridge.hashAfter input i) :
    StackRunBridge.hashAt32 (nextState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) :=
  PairedBlockModel.resultState_hash s input i h ctx

noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (_hpositive : 0 < input.size)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned (nextState s input i) input i) := by
  have gcompress := PairedBlockTrace.gasSteps_compress s input i h hfit hi ctx
    hcode hfork hrun hnp
  exact GasSteps.cast gcompress (by rfl) (by
    rfl)

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := nextState
  executionEnv := nextState_executionEnv
  halt := nextState_halt
  callStack := nextState_callStack
  activeWords := by
    intro s input i hfit hi
    exact PairTableActive.loaded_active_mono s (PairedBlockModel.messagePointer i)
      (PairedBlockModel.messagePointer_bound input hfit i hi)
  wordAbove := nextState_word_above
  hashResult := nextState_hash
  double := fun _ => false
  gasSteps := fun s input i h hfit hi ctx hcode hfork hrun hnp _ hpositive =>
    gasSteps_block s input i h hfit hi ctx hpositive hcode hfork hrun hnp
  nextState2 := fun s _ => s
  executionEnv2 := by intros; rfl
  halt2 := by intros; rfl
  callStack2 := by intros; rfl
  activeWords2 := by intros; exact Nat.le_refl _
  wordAbove2 := by intros; rfl
  doubleBlocks := by intro _ hd; cases hd
  hashResult2 := by intro _ _ hd; cases hd
  gasSteps2 := by intro _ _ _ _ hd; cases hd

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 272)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hempty : input.size = 0
  · exact DirectEmptyReturn.correct_empty input hfit hempty entryPrefix
  · exact StackRunBridge.correct_of_block_kernel kernel input hfit (Nat.pos_of_ne_zero hempty) entryPrefix

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
