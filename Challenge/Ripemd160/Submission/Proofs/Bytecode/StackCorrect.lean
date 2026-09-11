import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Execution
import Challenge.Ripemd160.Submission.Proofs.Bytecode.TinyGuard

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

/-- Mathematical single-block state for the hash invariant. Nonempty inputs
execute the generic compressor. The empty case returns through TinyGuard
and retains this abstract state only for the common hash-state interface. -/
def nextState (s : State) (input : ByteArray) (i : Nat) : State :=
  if input.size = 0 then FastEmptyBlock.resultState s input i
  else PairedBlockModel.resultState s input i

@[simp] theorem nextState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).executionEnv = s.executionEnv := by
  unfold nextState
  split <;> simp

@[simp] theorem nextState_halt (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).halt = s.halt := by
  unfold nextState
  split <;> simp

@[simp] theorem nextState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).callStack = s.callStack := by
  unfold nextState
  split <;> simp

theorem nextState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x2e0 ≤ address) :
    StackRunBridge.wordAt (nextState s input i) address =
      StackRunBridge.wordAt s address := by
  unfold nextState
  split
  · exact FastEmptyBlock.resultState_word_above _ _ _ _ (by omega)
  · exact PairedBlockModel.resultState_word_above _ _ _ _ haddress

private theorem input_eq_empty (input : ByteArray) (hempty : input.size = 0) :
    input = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using hempty
  · intro i hi
    simp [hempty] at hi

theorem nextState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (_hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hmodel : CompressionCorrect.hashArray h = CompressionSeamBridge.hashAfter input i) :
    StackRunBridge.hashAt32 (nextState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  unfold nextState
  by_cases hempty : input.size = 0
  · rw [if_pos hempty]
    have hinput := input_eq_empty input hempty
    subst input
    have hi0 : i = 0 := by
      simp [DriverTrace.blockCount, Padding.paddedLength] at hi
      omega
    subst i
    change StackMemory.hashAt (FastEmptyBlock.resultState s ByteArray.empty 0).memory = _
    rw [FastEmptyBlock.resultState_hashAt, hmodel]
    change FastEmptyBlock.emptyHash = StackRunBridge.embedHashArray
      (Crypto.Ripemd160.compressBlock Crypto.Ripemd160.H0 (Padding.paddedMessage ByteArray.empty) 0)
    rw [FastEmptyBlock.compress_empty]
    rfl
  · rw [if_neg hempty]
    exact PairedBlockModel.resultState_hash _ _ _ _ ctx

noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hpositive : 0 < input.size)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned (nextState s input i) input i) := by
  have hempty : input.size ≠ 0 := Nat.ne_of_gt hpositive
  have gdispatch := FastEmptyBlock.gasSteps_nonempty s input i hfit
    hpositive ctx.calldata hcode hfork hrun hnp
  have gcompress := PairedBlockTrace.gasSteps_compress s input i h hfit hi ctx
    hcode hfork hrun hnp
  have hentry : FastEmptyBlock.nonemptyEntry s input i =
      DriverTrace.compressEntry s input i := by rfl
  rw [hentry] at gdispatch
  exact GasSteps.cast (gdispatch.trans gcompress) (by rfl) (by
    simp [nextState, hempty, DriverTrace.compressReturned])

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := nextState
  executionEnv := nextState_executionEnv
  halt := nextState_halt
  callStack := nextState_callStack
  wordAbove := nextState_word_above
  hashResult := nextState_hash
  double := fun _ => false
  gasSteps := fun s input i h hfit hi ctx hcode hfork hrun hnp _ hpositive =>
    gasSteps_block s input i h hfit hi ctx hpositive hcode hfork hrun hnp
  nextState2 := fun s _ => s
  executionEnv2 := by intros; rfl
  halt2 := by intros; rfl
  callStack2 := by intros; rfl
  wordAbove2 := by intros; rfl
  doubleBlocks := by intro _ hd; cases hd
  hashResult2 := by intro _ _ hd; cases hd
  gasSteps2 := by intro _ _ _ _ hd; cases hd

theorem correct (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 393)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  by_cases hhit : TinyGuardLogic.condition input = 0
  · exact TinyGuard.correct_hit input hfit hhit entryPrefix
  · have hnonempty : 0 < input.size := by
      by_contra h
      have he : input = ByteArray.empty := TinyGuardLogic.input_eq_empty input (by omega)
      exact hhit (he ▸ TinyGuardLogic.condition_empty)
    exact StackRunBridge.correct_of_block_kernel kernel input hfit hnonempty
      (entryPrefix.trans (TinyGuard.gasSteps_miss input hhit))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
