import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixedPC5
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open YulEvmCompiler

private theorem instructionPC_succ
    (p : Challenge.EvmProof.ProgramArtifact) (index : Nat) (instr : Instr)
    (hget : p.instructions[index]? = some instr) :
    p.instructionPC (index + 1) =
      p.instructionPC index + instr.bytes.length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC,
    List.take_add_one, hget, Option.toList_some, assembleBytes_append,
    assembleBytes_cons, assembleBytes_nil, List.append_nil, List.length_append]

@[simp] theorem earlyExtraPC3921 : Artifact.submissionArtifact.instructionPC 3333 = 4398 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC3922 : Artifact.submissionArtifact.instructionPC 3334 = 4399 := by
  calc
    Artifact.submissionArtifact.instructionPC 3334 =
        Artifact.submissionArtifact.instructionPC 3333 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3333 (.op .JUMPDEST) (by rfl)
    _ = 4399 := by rw [earlyExtraPC3921]; rfl

@[simp] theorem earlyExtraPC3923 : Artifact.submissionArtifact.instructionPC 3335 = 4402 := by
  calc
    Artifact.submissionArtifact.instructionPC 3335 =
        Artifact.submissionArtifact.instructionPC 3334 + ((.push 2 2112) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3334 (.push 2 2112) (by rfl)
    _ = 4402 := by rw [earlyExtraPC3922]; rfl

@[simp] theorem earlyExtraPC3924 : Artifact.submissionArtifact.instructionPC 3336 = 4405 := by
  calc
    Artifact.submissionArtifact.instructionPC 3336 =
        Artifact.submissionArtifact.instructionPC 3335 + ((.push 2 2688) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3335 (.push 2 2688) (by rfl)
    _ = 4405 := by rw [earlyExtraPC3923]; rfl

@[simp] theorem earlyExtraPC3925 : Artifact.submissionArtifact.instructionPC 3337 = 4406 := by
  calc
    Artifact.submissionArtifact.instructionPC 3337 =
        Artifact.submissionArtifact.instructionPC 3336 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3336 (.op .MLOAD) (by rfl)
    _ = 4406 := by rw [earlyExtraPC3924]; rfl

@[simp] theorem earlyExtraPC3926 : Artifact.submissionArtifact.instructionPC 3338 = 4407 := by
  calc
    Artifact.submissionArtifact.instructionPC 3338 =
        Artifact.submissionArtifact.instructionPC 3337 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3337 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4407 := by rw [earlyExtraPC3925]; rfl

@[simp] theorem earlyExtraPC3927 : Artifact.submissionArtifact.instructionPC 3339 = 4408 := by
  calc
    Artifact.submissionArtifact.instructionPC 3339 =
        Artifact.submissionArtifact.instructionPC 3338 + ((.op .MCOPY) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3338 (.op .MCOPY) (by rfl)
    _ = 4408 := by rw [earlyExtraPC3926]; rfl

@[simp] theorem earlyExtraPC3928 : Artifact.submissionArtifact.instructionPC 3616 = 4772 := by
  calc
    Artifact.submissionArtifact.instructionPC 3616 =
        Artifact.submissionArtifact.instructionPC 3615 + ((.op .JUMP) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3615 (.op .JUMP) (by rfl)
    _ = 4772 := by rw [earlyExtraPC3920]; rfl

end Challenge.Modexp.Submission.Proofs.Fast
