import Challenge.Modexp.Submission.Proofs.Cycle.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.CodeCopy
import Challenge.Modexp.Submission.Proofs.Bytecode.Msize
import Challenge.Modexp.Submission.Proofs.Bytecode.MemoCert
import Challenge.Modexp.ProofSupport.InitialState
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 8000000
namespace CycleSubmission.MemoAnswer
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel WindowTwentyOneBinding
def preProgram : List Instr := [
  .push 32 26689440342447178617115869845918039756797228267049433585260346420242739014315,
  .push 0 0,
  .op .MSTORE]
def postProgram : List Instr := [
  .push 0 0,
   .op .RETURN]
def pre : Block Artifact.artifact .Osaka 1185 preProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 857 3 1185 preProgram
    (by decide) (by rfl) (by rfl) (by decide)
def post : Block Artifact.artifact .Osaka 1221 postProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 861 2 1221 postProgram
    (by decide) (by rfl) (by rfl) (by decide)
def answerBytes : ByteArray := Data.Bytes.natToBytesPadded MemoCert.answer 32
def entry (input : ByteArray) : State :=
  {initialState Artifact.bytecode input 0 with pc := UInt256.ofNat 1185}
def copied (input : ByteArray) : State :=
  {entry input with
    pc := UInt256.ofNat 1220
    memory := MachineState.writeBytes ByteArray.empty answerBytes 0
    activeWords := 1}
def sized (input : ByteArray) : State :=
  {copied input with pc := UInt256.ofNat 1221,stack := [32]}
def finalState (input : ByteArray) : State :=
  {sized input with
    pc := UInt256.ofNat 1222
    stack := []
    halt := .Returned
    hReturn := MachineState.readPadded (copied input).memory 0 32}
def envEntry (input : ByteArray) : Environment Artifact.artifact .Osaka (entry input) where
  sizeBound := by rw [show Artifact.artifact.code = Artifact.bytecode from rfl,Artifact.bytecodeSize]; decide
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile
theorem run_pre (input : ByteArray) :
    runInstructions preProgram (entry input) = some (copied input) := by rfl
def steps_pre (input : ByteArray) : GasSteps (entry input) (copied input) :=
  pre.steps (envEntry input) rfl (run_pre input)
theorem size_decodes (input : ByteArray) : (copied input).decodedOp = some .MSIZE := by
  have h := Stepper.decodes_of_artifact Artifact.artifact (copied input) 860 (.op .MSIZE)
    rfl (by rfl) (by rfl) (by exact ⟨by decide,by trivial,by rfl⟩)
  exact h
def steps_size (input : ByteArray) : GasSteps (copied input) (sized input) := by
  exact Msize.step (size_decodes input) (by change 0 < 1024; decide) rfl deployAddress_not_precompile
theorem run_post (input : ByteArray) :
    runInstructions postProgram (sized input) = some (finalState input) := by rfl
def steps_post (input : ByteArray) : GasSteps (sized input) (finalState input) :=
  post.steps ((envEntry input).transfer rfl rfl) rfl (run_post input)
/-- Full execution of the exact direct-store/MSIZE answer tail, including gas. -/
def steps (input : ByteArray) : GasSteps (entry input) (finalState input) :=
  (steps_pre input).trans ((steps_size input).trans (steps_post input))
theorem result (input : ByteArray) (hvalid : ValidInput input) (hmatch : MemoLogic.Matches input) :
    (finalState input).isDone = true ∧
      (finalState input).toResult = .returned (Challenge.Modexp.spec input) := by
  refine ⟨rfl,?_⟩
  rw [MemoCert.spec_eq input hvalid hmatch]
  have hs : answerBytes.size = 32 := by simp [answerBytes,Data.Bytes.natToBytesPadded,ByteArray.size]
  have h := Memory.readPadded_writeBytes_same ByteArray.empty answerBytes 0
  rw [hs] at h
  change ExecutionResult.returned (MachineState.readPadded
    (MachineState.writeBytes ByteArray.empty answerBytes 0) 0 32) = _
  rw [h]
  rfl
#print axioms steps
#print axioms result
end CycleSubmission.MemoAnswer
