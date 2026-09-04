import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLane
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTailTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open StackBlockModel StackEndpoint PairLane StackLoadSeams

private theorem returnPC : Artifact.submissionArtifact.instructionPC 783 = 0x643 := by
  rw [StackPC.instructionPC_eq_byteLength]
  decide

noncomputable def gasSteps_legacyBlock (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input) (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned (resultState s input i) input i) := by
  let q := scheduledState s input i
  let word := blockWords input i
  let w := initialWorking q
  let rest := StackFrame.frameRest input i
  let left := StackCompression.leftRounds word 80 w
  let right := StackCompression.rightRounds word 80 w
  let rightRest := StackRoundTrace.roundWords left ++ rest
  have qactive : 67 ≤ q.activeWords.toNat := by
    rw [scheduledState_activeWords s input hfit i hi]
    omega
  have qwords : WordsAt q word := scheduled_words_memory s input i h ctx
  have qenv : q.executionEnv = s.executionEnv := by
    exact Schedule.loopState_executionEnv s _ _ _ 16
  have qcode : q.executionEnv.code = submissionBytecode := by rw [qenv]; exact hcode
  have qfork : q.fork = .Osaka := by rw [State.fork, qenv]; exact hfork
  have qrun : q.halt = .Running := by
    exact (Schedule.loopState_halt s (DriverTrace.messageOffsetWord i)
      (UInt256.ofNat 0x72f) (scheduleRest input i) 16).trans hrun
  have qnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig
      q.executionEnv.fork q.executionEnv.codeAddr = false := by rw [qenv]; exact hnp
  have restBound : rest.length < 1012 := by
    simp [rest, StackFrame.frameRest, driverRest]
  have rightRestBound : rightRest.length < 1012 := by
    simp [rightRest, StackRoundTrace.roundWords, rest, StackFrame.frameRest, driverRest]
  have gframe := StackFrame.gasSteps_frame s input i hfit hi hcode hfork hrun hnp
  have gload1 := StackLoadTrace.gasSteps_load StackFrame.loadSite986 q rest qactive
    (by omega) qcode qfork qrun qnp
  have gload1' : GasSteps (StackFrame.frameLoadEntry s input i)
      (stateAt q (PairSites.leftPC 0) w rest) := by
    exact gload1.cast (firstLoad_entry s input i) (firstLoad_returned q rest)
  have gleft := gasSteps_left80 q word w rest qwords qactive restBound qcode qfork qrun qnp
  have gload2 := StackLoadTrace.gasSteps_load StackFrame.loadSite1476 q rightRest qactive
    (by omega) qcode qfork qrun qnp
  have gload2' : GasSteps (stateAt q (PairSites.leftPC 40) left rest)
      (stateAt q (PairSites.rightPC 0) w rightRest) := by
    exact gload2.cast (secondLoad_entry q left rest) (secondLoad_returned q rightRest)
  have gright := gasSteps_right80 q word w rightRest qwords qactive rightRestBound
    qcode qfork qrun qnp
  have hvalid : Decode.isValidJumpDest q.executionEnv.code
      (UInt256.ofNat 0x643).toNat = true := by
    have hdest := Artifact.submissionArtifact.isValidJumpDest_index 783 (by rfl)
    rw [returnPC] at hdest
    change Decode.isValidJumpDest q.executionEnv.code 0x643 = true
    rw [qcode]
    exact hdest
  have gtail := StackTailTrace.actualTailGasSteps q left right (UInt256.ofNat 0x643)
    (driverRest input i) qactive (by simp [driverRest]) qcode qfork qrun qnp hvalid
  have tailSeam : stateAt q (PairSites.rightPC 40) right rightRest =
      StackTail.tailEntry q left right (UInt256.ofNat 0x643) (driverRest input i) := by
    exact (tailEntry_atLanePC q left right (UInt256.ofNat 0x643) (driverRest input i)).symm
  have hleft : left = leftWorking s input i := by
    exact congrArg (StackCompression.leftRounds (blockWords input i) 80)
      (initialWorking_scheduled s input i)
  have hright : right = rightWorking s input i := by
    exact congrArg (StackCompression.rightRounds (blockWords input i) 80)
      (initialWorking_scheduled s input i)
  have tailEnd : StackTailTrace.actualTailResult q left right (UInt256.ofNat 0x643)
      (driverRest input i) =
      DriverTrace.compressReturned (resultState s input i) input i := by
    exact (congrArg₂ (fun l r => StackTail.tailResult q l r (UInt256.ofNat 0x643)
      (driverRest input i)) hleft hright).trans
      ((tailResult_eq_resultState s input i).trans (resultState_returned s input i))
  exact gframe.trans (gload1'.trans (gleft.trans (gload2'.trans
    (gright.trans (gtail.cast tailSeam.symm tailEnd)))))

def nextState (s : State) (input : ByteArray) (i : Nat) : State :=
  if input.size = 0 then FastEmptyBlock.resultState s input i
  else resultState s input i

@[simp] theorem nextState_executionEnv (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).executionEnv = s.executionEnv := by
  simp [nextState]

@[simp] theorem nextState_halt (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).halt = s.halt := by
  simp [nextState]

@[simp] theorem nextState_callStack (s : State) (input : ByteArray) (i : Nat) :
    (nextState s input i).callStack = s.callStack := by
  simp [nextState]

theorem nextState_word_above (s : State) (input : ByteArray) (i address : Nat)
    (haddress : 0x4a0 ≤ address) :
    StackRunBridge.wordAt (nextState s input i) address =
      StackRunBridge.wordAt s address := by
  by_cases hempty : input.size = 0
  · simp only [nextState, hempty, if_pos]
    exact FastEmptyBlock.resultState_word_above s input i address haddress
  · simp only [nextState, hempty, if_neg]
    exact resultState_word_above s input i address haddress

private theorem input_eq_empty (input : ByteArray) (hempty : input.size = 0) :
    input = ByteArray.empty := by
  apply ByteArray.ext
  apply Array.ext
  · simpa using hempty
  · intro i hi
    simp [hempty] at hi

theorem nextState_hash (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hmodel : CompressionCorrect.hashArray h =
      CompressionSeamBridge.hashAfter input i) :
    StackRunBridge.hashAt32 (nextState s input i) =
      StackRunBridge.embedHashArray
        (Crypto.Ripemd160.compressBlock (CompressionCorrect.hashArray h)
          (Padding.paddedMessage input) (DriverTrace.blockOffset i)) := by
  by_cases hempty : input.size = 0
  · have hinput := input_eq_empty input hempty
    subst input
    have hi0 : i = 0 := by
      simp [DriverTrace.blockCount, Padding.paddedLength] at hi
      omega
    subst i
    simp only [nextState, ByteArray.size_empty, if_pos rfl]
    change StackMemory.hashAt (FastEmptyBlock.resultState s ByteArray.empty 0).memory = _
    rw [FastEmptyBlock.resultState_hashAt, hmodel]
    decide
  · simp only [nextState, hempty, if_neg]
    exact resultState_hash s input i h ctx

noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (hfit : CalldataFits input)
    (hi : i < DriverTrace.blockCount input)
    (ctx : StackRunBridge.BlockContext s input i h)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.dispatchEntry s input i)
      (DriverTrace.compressReturned (nextState s input i) input i) := by
  by_cases hempty : input.size = 0
  · have gempty := FastEmptyBlock.gasSteps_empty s input i hempty
      ctx.calldata hcode hfork hrun hnp
    exact GasSteps.cast gempty rfl (by
      simp [nextState, hempty, DriverTrace.compressReturned,
        FastEmptyBlock.resultState])
  · have gdispatch := FastEmptyBlock.gasSteps_nonempty s input i hfit
      (Nat.pos_of_ne_zero hempty) ctx.calldata hcode hfork hrun hnp
    have glegacy := gasSteps_legacyBlock s input i h hfit hi ctx hcode hfork
      hrun hnp
    exact GasSteps.cast (gdispatch.trans glegacy) rfl (by
      simp [nextState, hempty])

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := nextState
  executionEnv := nextState_executionEnv
  halt := nextState_halt
  callStack := nextState_callStack
  wordAbove := nextState_word_above
  hashResult := fun s input i h hfit hi ctx hmodel =>
    nextState_hash s input i h hfit hi ctx hmodel
  gasSteps := gasSteps_block

theorem correct : Correct submissionBytecode := StackRunBridge.correct_of_block_kernel kernel

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
