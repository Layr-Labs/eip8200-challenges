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

def preProgram : List Instr := [.push 1 32, .push 4 62, .push 0 0]
def postProgram : List Instr := [.push 0 0, .op .RETURN]

def pre : Block Artifact.artifact .Osaka 733 preProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 505 3 733 preProgram
    (by decide) (by rfl) (by rfl) (by decide)
def post : Block Artifact.artifact .Osaka 743 postProgram :=
  WindowTwentyOneSlice.block Artifact.wellFormed 510 2 743 postProgram
    (by decide) (by rfl) (by rfl) (by decide)

def answerBytes : ByteArray := Data.Bytes.natToBytesPadded MemoCert.answer 32

private def memoPrefix : ByteArray := ByteArray.mk #[0x60, 0x22, 0x35, 0x60, 0x40, 0x35, 0x01, 0x62, 0x20, 0x00, 0x20, 0x18, 0x61, 0x02, 0x42, 0x57, 0x60, 0x60, 0x35, 0x60, 0x80, 0x35, 0x60, 0xa0, 0x35, 0x81, 0x81, 0x03, 0x61, 0x1f, 0xff, 0x60, 0x01, 0x35, 0x03, 0x1c, 0x61, 0x02, 0xe9, 0x57, 0x5f, 0x35, 0x60, 0x20, 0x18, 0x60, 0x65, 0x57, 0x5b, 0x81, 0x19, 0x81, 0x01, 0x61, 0x02, 0xe9, 0x57, 0x61, 0x29, 0x4f, 0x56, 0x7f, 0x3b, 0x01, 0xb0, 0x1a, 0xc4, 0x1f, 0x2d, 0x6e, 0x91, 0x7c, 0x6d, 0x6a, 0x22, 0x1c, 0xe7, 0x93, 0x80, 0x24, 0x69, 0x02, 0x6d, 0x9a, 0xb7, 0x57, 0x8f, 0xa2, 0xe7, 0x9e, 0x4d, 0xa6, 0xaa, 0xab, 0x5f, 0x60, 0x00, 0x60, 0x00, 0x5b, 0x5b, 0x5b, 0x60, 0x20, 0x5f, 0x35, 0x81, 0x81, 0x11, 0x60, 0xdb, 0x57, 0x90, 0x03, 0x60, 0x60, 0x35, 0x81, 0x60, 0x03, 0x1b, 0x1c, 0x81, 0x60, 0x80, 0x03, 0x35, 0x82]

private theorem prefixSplit : ∃ tail : ByteArray, Artifact.bytecode = memoPrefix ++ tail := by
  unfold Artifact.bytecode
  simp only [ByteArray.append_assoc]
  rw [← ByteArray.append_assoc]
  exact ⟨_, rfl⟩

theorem answerSlice : MachineState.readPadded Artifact.bytecode 62 32 = answerBytes := by
  obtain ⟨tail, ht⟩ := prefixSplit
  have h : MachineState.readPadded Artifact.bytecode 62 32 =
      MachineState.readPadded memoPrefix 62 32 := by
    rw [ht]
    apply Memory.readPadded_congr
    intro i hi
    rw [Memory.getElem?_getD_append]
    have hbound : 62 + i < memoPrefix.size := by change 62 + i < 128; omega
    rw [if_pos hbound]
  rw [h]
  unfold answerBytes
  rw [Memory.natToBytesPadded_eq_natToBE]
  rfl

def entry (input : ByteArray) : State :=
  {initialState Artifact.bytecode input 0 with pc := UInt256.ofNat 733}
def copyArgs (input : ByteArray) : State :=
  {entry input with pc := UInt256.ofNat 741, stack := [0, 62, 32]}
def copied (input : ByteArray) : State :=
  {entry input with
    pc := UInt256.ofNat 742
    memory := MachineState.writeBytes ByteArray.empty answerBytes 0
    activeWords := 1}
def sized (input : ByteArray) : State :=
  {copied input with pc := UInt256.ofNat 743, stack := [32]}
def finalState (input : ByteArray) : State :=
  {sized input with
    pc := UInt256.ofNat 744
    stack := []
    halt := .Returned
    hReturn := MachineState.readPadded (copied input).memory 0 32}

def envEntry (input : ByteArray) : Environment Artifact.artifact .Osaka (entry input) where
  sizeBound := by rw [show Artifact.artifact.code = Artifact.bytecode from rfl, Artifact.bytecodeSize]; decide
  code := rfl
  forkEq := rfl
  running := rfl
  noPrecompile := deployAddress_not_precompile

theorem run_pre (input : ByteArray) :
    runInstructions preProgram (entry input) = some (copyArgs input) := by rfl

def steps_pre (input : ByteArray) : GasSteps (entry input) (copyArgs input) :=
  pre.steps (envEntry input) rfl (run_pre input)

theorem copy_decodes (input : ByteArray) : (copyArgs input).decodedOp = some .CODECOPY := by
  have h := Stepper.decodes_of_artifact Artifact.artifact (copyArgs input) 508 (.op .CODECOPY)
    rfl (by rfl) (by rfl) (by exact ⟨by decide, by trivial, by rfl⟩)
  exact h

def steps_copy (input : ByteArray) : GasSteps (copyArgs input) (copied input) := by
  have h := CodeCopy.step (s := copyArgs input) (dest := 0) (src := 62) (size := 32)
    (rest := []) (copy_decodes input) rfl (by change 3 + 0 ≤ 1024 + 3; decide) rfl deployAddress_not_precompile
  have hr : MachineState.readPadded (copyArgs input).executionEnv.code
      (62 : UInt256).toNat (32 : UInt256).toNat = answerBytes := answerSlice
  rw [hr] at h
  exact h

theorem size_decodes (input : ByteArray) : (copied input).decodedOp = some .MSIZE := by
  have h := Stepper.decodes_of_artifact Artifact.artifact (copied input) 509 (.op .MSIZE)
    rfl (by rfl) (by rfl) (by exact ⟨by decide, by trivial, by rfl⟩)
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
  refine ⟨rfl, ?_⟩
  rw [MemoCert.spec_eq input hvalid hmatch]
  have hs : answerBytes.size = 32 := by simp [answerBytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  have h := Memory.readPadded_writeBytes_same ByteArray.empty answerBytes 0
  rw [hs] at h
  change ExecutionResult.returned (MachineState.readPadded
    (MachineState.writeBytes ByteArray.empty answerBytes 0) 0 32) = _
  rw [h]
  rfl

#print axioms steps
#print axioms result
end CycleSubmission.MemoAnswer
