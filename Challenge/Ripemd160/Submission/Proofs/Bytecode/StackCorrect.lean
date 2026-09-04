import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackLoadSeams
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairLane
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackTailTrace

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 1000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open StackBlockModel StackEndpoint PairLane StackLoadSeams

private theorem returnPC : Artifact.submissionArtifact.instructionPC 783 = 0x643 := by
  rw [StackPC.instructionPC_eq_byteLength]
  decide

noncomputable def gasSteps_block (s : State) (input : ByteArray) (i : Nat)
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
  have qactive : 66 ≤ q.activeWords.toNat := by
    rw [scheduledState_activeWords s input hfit i hi]
    omega
  have qwords : WordsAt q word := scheduled_words_memory s input i h ctx hfit hi
  have qenv : q.executionEnv = s.executionEnv := by
    simp only [q, scheduledState, withActiveWords_executionEnv,
      withMemory_executionEnv, Schedule.loopState_executionEnv]
  have qcode : q.executionEnv.code = submissionBytecode := by rw [qenv]; exact hcode
  have qfork : q.fork = .Osaka := by rw [State.fork, qenv]; exact hfork
  have qrun : q.halt = .Running := by
    simp only [q, scheduledState, withActiveWords_halt, withMemory_halt,
      Schedule.loopState_halt, hrun]
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

noncomputable def kernel : StackRunBridge.BlockKernel where
  nextState := resultState
  executionEnv := resultState_executionEnv
  halt := resultState_halt
  callStack := resultState_callStack
  wordAbove := resultState_word_above
  hashResult := fun s input i h _ _ ctx => resultState_hash s input i h ctx
  gasSteps := gasSteps_block

theorem correct : Correct submissionBytecode := StackRunBridge.correct_of_block_kernel kernel

end Challenge.Ripemd160.Submission.Proofs.Bytecode.StackCorrect
