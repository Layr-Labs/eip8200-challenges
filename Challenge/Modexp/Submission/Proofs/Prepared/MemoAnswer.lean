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
  .push 1 32,
   .push 1 61,
   .push 0 0]
def postProgram : List Instr := [
  .push 0 0,
   .op .RETURN]
def pre : Block Artifact.artifact .Osaka 937 preProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 658 3 937 preProgram
    (by decide) (by rfl) (by rfl) (by decide)
def post : Block Artifact.artifact .Osaka 944 postProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 663 2 944 postProgram
    (by decide) (by rfl) (by rfl) (by decide)
def answerBytes : ByteArray := Data.Bytes.natToBytesPadded MemoCert.answer 32
private def memoPrefix : ByteArray := ByteArray.mk #[96,34,53,96,64,53,1,98,32,0,32,24,97,2,52,87,96,96,53,96,128,53,96,160,53,129,129,3,97,31,255,96,1,53,3,28,97,3,178,87,95,53,96,32,24,96,96,87,91,129,129,20,97,3,178,87,97,41,128,86,127,59,1,176,26,196,31,45,110,145,124,109,106,34,28,231,147,128,36,105,2,109,154,183,87,143,162,231,158,77,166,170,171,95,91,91,91,96,32,95,53,129,129,17,96,207,87,144,3,96,96,53,129,96,3,27,28,129,96,128,3,53,130,96,160,3,53,97]
private theorem prefixSplit : ∃ tail : ByteArray,Artifact.bytecode = memoPrefix++tail := by
  unfold Artifact.bytecode
  simp only [ByteArray.append_assoc]
  rw [← ByteArray.append_assoc]
  exact ⟨_,rfl⟩
theorem answerSlice : MachineState.readPadded Artifact.bytecode 61 32 = answerBytes := by
  obtain ⟨tail,ht⟩ := prefixSplit
  have h : MachineState.readPadded Artifact.bytecode 61 32 =
      MachineState.readPadded memoPrefix 61 32 := by
    rw [ht]
    apply Memory.readPadded_congr
    intro i hi
    rw [Memory.getElem?_getD_append]
    have hbound : 61 + i < memoPrefix.size := by change 61 + i < 128; omega
    rw [if_pos hbound]
  rw [h]
  unfold answerBytes
  rw [Memory.natToBytesPadded_eq_natToBE]
  rfl
def entry (input : ByteArray) : State :=
  {initialState Artifact.bytecode input 0 with pc := UInt256.ofNat 937}
def copyArgs (input : ByteArray) : State :=
  {entry input with pc := UInt256.ofNat 942,stack := [0,61,32]}
def copied (input : ByteArray) : State :=
  {entry input with
    pc := UInt256.ofNat 943
    memory := MachineState.writeBytes ByteArray.empty answerBytes 0
    activeWords := 1}
def sized (input : ByteArray) : State :=
  {copied input with pc := UInt256.ofNat 944,stack := [32]}
def finalState (input : ByteArray) : State :=
  {sized input with
    pc := UInt256.ofNat 945
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
    runInstructions preProgram (entry input) = some (copyArgs input) := by rfl
def steps_pre (input : ByteArray) : GasSteps (entry input) (copyArgs input) :=
  pre.steps (envEntry input) rfl (run_pre input)
theorem copy_decodes (input : ByteArray) : (copyArgs input).decodedOp = some .CODECOPY := by
  have h := Stepper.decodes_of_artifact Artifact.artifact (copyArgs input) 661 (.op .CODECOPY)
    rfl (by rfl) (by rfl) (by exact ⟨by decide,by trivial,by rfl⟩)
  exact h
def steps_copy (input : ByteArray) : GasSteps (copyArgs input) (copied input) := by
  have h := CodeCopy.step (s := copyArgs input) (dest := 0) (src := 61) (size := 32)
    (rest := []) (copy_decodes input) rfl (by change 3 + 0 ≤ 1024 + 3; decide) rfl deployAddress_not_precompile
  have hr : MachineState.readPadded (copyArgs input).executionEnv.code
      (61 : UInt256).toNat (32 : UInt256).toNat = answerBytes := answerSlice
  rw [hr] at h
  exact h
theorem size_decodes (input : ByteArray) : (copied input).decodedOp = some .MSIZE := by
  have h := Stepper.decodes_of_artifact Artifact.artifact (copied input) 662 (.op .MSIZE)
    rfl (by rfl) (by rfl) (by exact ⟨by decide,by trivial,by rfl⟩)
  exact h
def steps_size (input : ByteArray) : GasSteps (copied input) (sized input) := by
  exact Msize.step (size_decodes input) (by change 0 < 1024; decide) rfl deployAddress_not_precompile
theorem run_post (input : ByteArray) :
    runInstructions postProgram (sized input) = some (finalState input) := by rfl
def steps_post (input : ByteArray) : GasSteps (sized input) (finalState input) :=
  post.steps ((envEntry input).transfer rfl rfl) rfl (run_post input)
/-- Full execution of the exact CODECOPY/MSIZE answer tail, including gas. -/
def steps (input : ByteArray) : GasSteps (entry input) (finalState input) :=
  (steps_pre input).trans ((steps_copy input).trans ((steps_size input).trans (steps_post input)))
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
