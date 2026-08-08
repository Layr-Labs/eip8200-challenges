import Challenge.Sha256.Submission.Proofs.Bytecode.DriverCorrect

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# End-to-end correctness of the frozen reference bytecode

This final layer connects the exact gas-parametric execution endpoint to the
reusable direct-bytecode obligation. Functional digest identification is
provided by `DriverCorrect`; the lemmas below isolate the orthogonal fact that
the reference program never creates a suspended caller frame.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ReferenceCorrect

open Challenge.Sha256.ProofSupport.Bytecode

open EvmSemantics
open EvmSemantics.EVM

@[simp] theorem afterCompression_callStack (s : State) (input : ByteArray)
    (i : Nat) :
    (Driver.afterCompression s input i).callStack = s.callStack := by
  simp [Driver.afterCompression, Driver.loopAt]

@[simp] theorem afterIteration_callStack (s : State) (input : ByteArray)
    (i : Nat) :
    (Driver.afterIteration s input i).callStack = s.callStack := by
  simp [Driver.afterIteration, Driver.loopAt]

@[simp] theorem blockLoopState_callStack (input : ByteArray) (i : Nat) :
    (Driver.blockLoopState input i).callStack = [] := by
  induction i with
  | zero => rfl
  | succ i ih => simp [Driver.blockLoopState, ih]

@[simp] theorem outputResult_callStack (s : State) (rest : List UInt256) :
    (Output.outputResult s rest).callStack = s.callStack := by
  rfl

/-- The exact gas-erased terminal state reached by the reference driver. -/
def finalState (input : ByteArray) : State :=
  Output.outputResult
    (Driver.blockLoopState input (Driver.blockCount input))
    [Padding.paddedWord input]

@[simp] theorem finalState_isDone (input : ByteArray) :
    (finalState input).isDone = true := by
  simp [finalState, State.isDone, State.isHalted, State.isRunning]

@[simp] theorem finalState_hReturn (input : ByteArray)
    (hfit : CalldataFits input) :
    (finalState input).hReturn = Challenge.Sha256.spec input := by
  simpa [finalState] using DriverCorrect.referenceOutput_correct input hfit

@[simp] theorem finalState_toResult (input : ByteArray)
    (hfit : CalldataFits input) :
    (finalState input).toResult = .returned (Challenge.Sha256.spec input) := by
  rw [State.toResult_returned _ (by simp [finalState])]
  rw [finalState_hReturn input hfit]

def gasSteps_finalState (input : ByteArray) (hfit : CalldataFits input) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (finalState input) := by
  simpa [finalState] using Driver.gasSteps_reference input hfit

@[simp] theorem withGas_initialState_zero (input : ByteArray) (gas : Nat) :
    Challenge.EvmProof.withGas (initialState submissionBytecode input 0) gas =
      initialState submissionBytecode input gas := by
  rfl

/-- The frozen reference bytes discharge the reusable direct-bytecode
obligation, with SHA computed entirely by the proved EVM instruction trace. -/
theorem referenceDirectProof : DirectProof submissionBytecode := by
  let Input := { calldata : ByteArray // CalldataFits calldata }
  have h := Challenge.EvmProof.GasSteps.toEventuallyEvaluates
    (initial := fun input : Input => initialState submissionBytecode input.1 0)
    (final := fun input : Input => finalState input.1)
    (expected := fun input : Input => .returned (Challenge.Sha256.spec input.1))
    (fun input => gasSteps_finalState input.1 input.2)
    (fun input => finalState_isDone input.1)
    (fun input => finalState_toResult input.1 input.2)
  simpa [DirectProof, Input] using h

theorem submissionDirectGoal_proved : submissionDirectGoal :=
  referenceDirectProof

/-- End-to-end canonical challenge theorem for the frozen reference bytecode. -/
theorem reference_correct : Correct submissionBytecode :=
  correct_of_directProof referenceDirectProof

end Challenge.Sha256.Submission.Proofs.Bytecode.ReferenceCorrect
