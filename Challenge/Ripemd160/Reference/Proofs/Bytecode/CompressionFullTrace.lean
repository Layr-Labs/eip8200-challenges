import Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionTailComposition
import Challenge.Ripemd160.Reference.Proofs.Bytecode.DriverTrace

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Complete compiled RIPEMD-160 compressor trace

This layer joins the schedule/left-line prefix to the right-line/tail suffix
and presents the result at the driver's compression-call seam.
-/

namespace Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionFullTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionRightTrace
open CompressionTailTrace

def driverRest (input : ByteArray) (i : Nat) : List UInt256 :=
  [DriverTrace.blockOffsetWord i, Padding.paddedWord input]

def resultState (s : State) (input : ByteArray) (i : Nat) : State :=
  let messageOffset := DriverTrace.messageOffsetWord i
  let returnDest := UInt256.ofNat 0x643
  let rest := driverRest input i
  CompressionTailTrace.rightTailResult
    (leftFinalState s messageOffset returnDest rest)
    messageOffset returnDest rest

private theorem leftFinalState_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (leftFinalState s messageOffset returnDest rest).executionEnv =
      s.executionEnv := by
  rw [leftFinalState, leftStates_executionEnv]
  simp [leftInitialState, copiedWorkingState, copyRegion, scheduledState]

private theorem leftFinalState_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (leftFinalState s messageOffset returnDest rest).halt = s.halt := by
  rw [leftFinalState, leftStates_halt]
  simp [leftInitialState, copiedWorkingState, copyRegion, scheduledState]

private theorem rightTailResult_executionEnv (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (rightTailResult s messageOffset returnDest rest).executionEnv =
      s.executionEnv := by
  rw [rightTailResult, combinationReturned, combinationCleaned,
    combination4_executionEnv, rightStates_executionEnv]

private theorem rightTailResult_halt (s : State)
    (messageOffset returnDest : UInt256) (rest : List UInt256) :
    (rightTailResult s messageOffset returnDest rest).halt = s.halt := by
  rw [rightTailResult, combinationReturned, combinationCleaned,
    combination4_halt, rightStates_halt]

@[simp] theorem resultState_executionEnv (s : State)
    (input : ByteArray) (i : Nat) :
    (resultState s input i).executionEnv = s.executionEnv := by
  rw [resultState, rightTailResult_executionEnv, leftFinalState_executionEnv]

@[simp] theorem resultState_halt (s : State) (input : ByteArray) (i : Nat) :
    (resultState s input i).halt = s.halt := by
  rw [resultState, rightTailResult_halt, leftFinalState_halt]

/-- One complete invocation of the compiled `compress` helper, normalized to
the exact return seam consumed by `DriverTrace`. -/
def gasSteps_compress (s : State) (input : ByteArray) (i : Nat)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompile s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned (resultState s input i) input i) := by
  let messageOffset := DriverTrace.messageOffsetWord i
  let returnDest := UInt256.ofNat 0x643
  let rest := driverRest input i
  have gleft := CompressionTrace.gasSteps_compressToRight s messageOffset
    returnDest rest (by simp [rest, driverRest]) hcode hfork hrun hnp
  let leftFinal := leftFinalState s messageOffset returnDest rest
  have hleftCode : leftFinal.executionEnv.code = referenceBytecode := by
    change (leftFinalState s messageOffset returnDest rest).executionEnv.code = _
    rw [leftFinalState_executionEnv]
    exact hcode
  have hleftFork : leftFinal.fork = .Osaka := by
    change (leftFinalState s messageOffset returnDest rest).fork = _
    rw [State.fork, leftFinalState_executionEnv]
    exact hfork
  have hleftRun : leftFinal.halt = .Running := by
    change (leftFinalState s messageOffset returnDest rest).halt = _
    rw [leftFinalState_halt]
    exact hrun
  have hleftNp : Precompile.isPrecompile leftFinal.executionEnv.fork
      leftFinal.executionEnv.codeAddr = false := by
    change Precompile.isPrecompile
      (leftFinalState s messageOffset returnDest rest).executionEnv.fork
      (leftFinalState s messageOffset returnDest rest).executionEnv.codeAddr = false
    rw [leftFinalState_executionEnv]
    exact hnp
  have gright := CompressionTailTrace.gasSteps_rightLoopAndTail leftFinal
    messageOffset returnDest rest (by simp [rest, driverRest]) hleftCode
    hleftFork hleftRun hleftNp (by decide)
  exact GasSteps.cast (gleft.trans gright)
    (by simp [DriverTrace.compressEntry, CompressionTrace.compressEntry,
      messageOffset, returnDest, rest, driverRest])
    (by simp [DriverTrace.compressReturned, resultState, messageOffset,
      returnDest, rest, driverRest, leftFinal, rightTailResult,
      combinationReturned])

end Challenge.Ripemd160.Reference.Proofs.Bytecode.CompressionFullTrace
