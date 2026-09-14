import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixedPC4
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

@[simp] theorem fixedPC3993 : Artifact.submissionArtifact.instructionPC 72 = 126 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5272 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 126 = true := by
  simpa only [Artifact.instructionPC, fixedPC3993] using Artifact.isValidJumpDest_index 72 (by rfl)

@[simp] theorem fixedPC3994 : Artifact.submissionArtifact.instructionPC 73 = 127 := by
  calc
    Artifact.submissionArtifact.instructionPC 73 =
        Artifact.submissionArtifact.instructionPC 72 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 72 (.op .JUMPDEST) (by rfl)
    _ = 127 := by rw [fixedPC3993]; rfl

@[simp] theorem fixedPC3995 : Artifact.submissionArtifact.instructionPC 74 = 128 := by
  calc
    Artifact.submissionArtifact.instructionPC 74 =
        Artifact.submissionArtifact.instructionPC 73 + ((.op .POP) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 73 (.op .POP) (by rfl)
    _ = 128 := by rw [fixedPC3994]; rfl

@[simp] theorem fixedPC3996 : Artifact.submissionArtifact.instructionPC 75 = 129 := by
  calc
    Artifact.submissionArtifact.instructionPC 75 =
        Artifact.submissionArtifact.instructionPC 74 + ((.op .POP) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 74 (.op .POP) (by rfl)
    _ = 129 := by rw [fixedPC3995]; rfl

@[simp] theorem fixedPC3997 : Artifact.submissionArtifact.instructionPC 76 = 130 := by
  calc
    Artifact.submissionArtifact.instructionPC 76 =
        Artifact.submissionArtifact.instructionPC 75 + ((.op .POP) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 75 (.op .POP) (by rfl)
    _ = 130 := by rw [fixedPC3996]; rfl

@[simp] theorem fixedPC3998 : Artifact.submissionArtifact.instructionPC 77 = 133 := by
  calc
    Artifact.submissionArtifact.instructionPC 77 =
        Artifact.submissionArtifact.instructionPC 76 + ((.push 2 709) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 76 (.push 2 709) (by rfl)
    _ = 133 := by rw [fixedPC3997]; rfl

@[simp] theorem fixedPC3999 : Artifact.submissionArtifact.instructionPC 3299 = 4341 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedJump5280 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4341 = true := by
  simpa only [Artifact.instructionPC, fixedPC3999] using Artifact.isValidJumpDest_index 3299 (by rfl)

@[simp] theorem fixedPC4000 : Artifact.submissionArtifact.instructionPC 3300 = 4342 := by
  calc
    Artifact.submissionArtifact.instructionPC 3300 =
        Artifact.submissionArtifact.instructionPC 3299 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3299 (.op .JUMPDEST) (by rfl)
    _ = 4342 := by rw [fixedPC3999]; rfl

@[simp] theorem fixedPC4001 : Artifact.submissionArtifact.instructionPC 3301 = 4345 := by
  calc
    Artifact.submissionArtifact.instructionPC 3301 =
        Artifact.submissionArtifact.instructionPC 3300 + ((.push 2 2208) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3300 (.push 2 2208) (by rfl)
    _ = 4345 := by rw [fixedPC4000]; rfl

@[simp] theorem fixedPC4002 : Artifact.submissionArtifact.instructionPC 3302 = 4346 := by
  calc
    Artifact.submissionArtifact.instructionPC 3302 =
        Artifact.submissionArtifact.instructionPC 3301 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3301 (.op .MLOAD) (by rfl)
    _ = 4346 := by rw [fixedPC4001]; rfl

@[simp] theorem fixedPC4003 : Artifact.submissionArtifact.instructionPC 3303 = 4348 := by
  calc
    Artifact.submissionArtifact.instructionPC 3303 =
        Artifact.submissionArtifact.instructionPC 3302 + ((.push 1 96) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3302 (.push 1 96) (by rfl)
    _ = 4348 := by rw [fixedPC4002]; rfl

@[simp] theorem fixedPC4004 : Artifact.submissionArtifact.instructionPC 3304 = 4349 := by
  calc
    Artifact.submissionArtifact.instructionPC 3304 =
        Artifact.submissionArtifact.instructionPC 3303 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3303 (.op .MLOAD) (by rfl)
    _ = 4349 := by rw [fixedPC4003]; rfl

@[simp] theorem fixedPC4005 : Artifact.submissionArtifact.instructionPC 3305 = 4350 := by
  calc
    Artifact.submissionArtifact.instructionPC 3305 =
        Artifact.submissionArtifact.instructionPC 3304 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3304 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4350 := by rw [fixedPC4004]; rfl

@[simp] theorem fixedPC4006 : Artifact.submissionArtifact.instructionPC 3306 = 4351 := by
  calc
    Artifact.submissionArtifact.instructionPC 3306 =
        Artifact.submissionArtifact.instructionPC 3305 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3305 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 4351 := by rw [fixedPC4005]; rfl

@[simp] theorem fixedPC4007 : Artifact.submissionArtifact.instructionPC 3307 = 4352 := by
  calc
    Artifact.submissionArtifact.instructionPC 3307 =
        Artifact.submissionArtifact.instructionPC 3306 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3306 (.op .GT) (by rfl)
    _ = 4352 := by rw [fixedPC4006]; rfl

@[simp] theorem fixedPC4008 : Artifact.submissionArtifact.instructionPC 3308 = 4353 := by
  calc
    Artifact.submissionArtifact.instructionPC 3308 =
        Artifact.submissionArtifact.instructionPC 3307 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3307 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4353 := by rw [fixedPC4007]; rfl

@[simp] theorem fixedPC4009 : Artifact.submissionArtifact.instructionPC 3309 = 4354 := by
  calc
    Artifact.submissionArtifact.instructionPC 3309 =
        Artifact.submissionArtifact.instructionPC 3308 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3308 (.op .SUB) (by rfl)
    _ = 4354 := by rw [fixedPC4008]; rfl

@[simp] theorem fixedPC4010 : Artifact.submissionArtifact.instructionPC 3310 = 4357 := by
  calc
    Artifact.submissionArtifact.instructionPC 3310 =
        Artifact.submissionArtifact.instructionPC 3309 + ((.push 2 1888) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3309 (.push 2 1888) (by rfl)
    _ = 4357 := by rw [fixedPC4009]; rfl

@[simp] theorem fixedPC4011 : Artifact.submissionArtifact.instructionPC 3311 = 4358 := by
  calc
    Artifact.submissionArtifact.instructionPC 3311 =
        Artifact.submissionArtifact.instructionPC 3310 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3310 (.op .MSTORE) (by rfl)
    _ = 4358 := by rw [fixedPC4010]; rfl

@[simp] theorem fixedPC4012 : Artifact.submissionArtifact.instructionPC 3312 = 4361 := by
  calc
    Artifact.submissionArtifact.instructionPC 3312 =
        Artifact.submissionArtifact.instructionPC 3311 + ((.push 2 4689) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3311 (.push 2 4689) (by rfl)
    _ = 4361 := by rw [fixedPC4011]; rfl

@[simp] theorem earlyExtraPC2880 : Artifact.submissionArtifact.instructionPC 2482 = 3295 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2883 : Artifact.submissionArtifact.instructionPC 3286 = 4320 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem earlyExtraPC2884 : Artifact.submissionArtifact.instructionPC 3287 = 4321 := by
  calc
    Artifact.submissionArtifact.instructionPC 3287 =
        Artifact.submissionArtifact.instructionPC 3286 + ((.op .JUMPDEST) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3286 (.op .JUMPDEST) (by rfl)
    _ = 4321 := by rw [earlyExtraPC2883]; rfl

@[simp] theorem earlyExtraPC2885 : Artifact.submissionArtifact.instructionPC 3288 = 4322 := by
  calc
    Artifact.submissionArtifact.instructionPC 3288 =
        Artifact.submissionArtifact.instructionPC 3287 + ((.push 0 0) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3287 (.push 0 0) (by rfl)
    _ = 4322 := by rw [earlyExtraPC2884]; rfl

@[simp] theorem earlyExtraPC2886 : Artifact.submissionArtifact.instructionPC 3289 = 4323 := by
  calc
    Artifact.submissionArtifact.instructionPC 3289 =
        Artifact.submissionArtifact.instructionPC 3288 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3288 (.op .MLOAD) (by rfl)
    _ = 4323 := by rw [earlyExtraPC2885]; rfl

@[simp] theorem earlyExtraPC2887 : Artifact.submissionArtifact.instructionPC 3290 = 4326 := by
  calc
    Artifact.submissionArtifact.instructionPC 3290 =
        Artifact.submissionArtifact.instructionPC 3289 + ((.push 2 2112) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3289 (.push 2 2112) (by rfl)
    _ = 4326 := by rw [earlyExtraPC2886]; rfl

@[simp] theorem earlyExtraPC2888 : Artifact.submissionArtifact.instructionPC 3291 = 4327 := by
  calc
    Artifact.submissionArtifact.instructionPC 3291 =
        Artifact.submissionArtifact.instructionPC 3290 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3290 (.op .MLOAD) (by rfl)
    _ = 4327 := by rw [earlyExtraPC2887]; rfl

@[simp] theorem earlyExtraPC2889 : Artifact.submissionArtifact.instructionPC 3292 = 4328 := by
  calc
    Artifact.submissionArtifact.instructionPC 3292 =
        Artifact.submissionArtifact.instructionPC 3291 + ((.op .LT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3291 (.op .LT) (by rfl)
    _ = 4328 := by rw [earlyExtraPC2888]; rfl

@[simp] theorem earlyExtraPC2890 : Artifact.submissionArtifact.instructionPC 3293 = 4331 := by
  calc
    Artifact.submissionArtifact.instructionPC 3293 =
        Artifact.submissionArtifact.instructionPC 3292 + ((.push 2 2080) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3292 (.push 2 2080) (by rfl)
    _ = 4331 := by rw [earlyExtraPC2889]; rfl

@[simp] theorem earlyExtraPC2891 : Artifact.submissionArtifact.instructionPC 3294 = 4332 := by
  calc
    Artifact.submissionArtifact.instructionPC 3294 =
        Artifact.submissionArtifact.instructionPC 3293 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3293 (.op .MLOAD) (by rfl)
    _ = 4332 := by rw [earlyExtraPC2890]; rfl

@[simp] theorem earlyExtraPC2892 : Artifact.submissionArtifact.instructionPC 3295 = 4333 := by
  calc
    Artifact.submissionArtifact.instructionPC 3295 =
        Artifact.submissionArtifact.instructionPC 3294 + ((.op .LT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3294 (.op .LT) (by rfl)
    _ = 4333 := by rw [earlyExtraPC2891]; rfl

@[simp] theorem earlyExtraPC2893 : Artifact.submissionArtifact.instructionPC 3295 = 4333 := by
  exact earlyExtraPC2892

@[simp] theorem earlyExtraPC2894 : Artifact.submissionArtifact.instructionPC 3296 = 4336 := by
  calc
    Artifact.submissionArtifact.instructionPC 3296 =
        Artifact.submissionArtifact.instructionPC 3295 + ((.push 2 4398) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3295 (.push 2 4398) (by rfl)
    _ = 4336 := by rw [earlyExtraPC2893]; rfl

@[simp] theorem earlyExtraPC2895 : Artifact.submissionArtifact.instructionPC 3297 = 4337 := by
  calc
    Artifact.submissionArtifact.instructionPC 3297 =
        Artifact.submissionArtifact.instructionPC 3296 + ((.op .JUMPI) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3296 (.op .JUMPI) (by rfl)
    _ = 4337 := by rw [earlyExtraPC2894]; rfl

@[simp] theorem earlyExtraPC2896 : Artifact.submissionArtifact.instructionPC 3298 = 4340 := by
  calc
    Artifact.submissionArtifact.instructionPC 3298 =
        Artifact.submissionArtifact.instructionPC 3297 + ((.push 2 4536) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3297 (.push 2 4536) (by rfl)
    _ = 4340 := by rw [earlyExtraPC2895]; rfl

@[simp] theorem earlyExtraPC2927 : Artifact.submissionArtifact.instructionPC 2482 = 3295 := by
  exact earlyExtraPC2880

@[simp] theorem earlyExtraPC2930 : Artifact.submissionArtifact.instructionPC 3299 = 4341 := by
  exact fixedPC3999

@[simp] theorem earlyExtraPC2931 : Artifact.submissionArtifact.instructionPC 3300 = 4342 := by
  exact fixedPC4000

@[simp] theorem earlyExtraPC2932 : Artifact.submissionArtifact.instructionPC 3301 = 4345 := by
  exact fixedPC4001

@[simp] theorem earlyExtraPC2933 : Artifact.submissionArtifact.instructionPC 3302 = 4346 := by
  exact fixedPC4002

@[simp] theorem earlyExtraPC2934 : Artifact.submissionArtifact.instructionPC 3303 = 4348 := by
  exact fixedPC4003

@[simp] theorem earlyExtraPC2935 : Artifact.submissionArtifact.instructionPC 3304 = 4349 := by
  exact fixedPC4004

@[simp] theorem earlyExtraPC2936 : Artifact.submissionArtifact.instructionPC 3305 = 4350 := by
  exact fixedPC4005

@[simp] theorem earlyExtraPC2937 : Artifact.submissionArtifact.instructionPC 3306 = 4351 := by
  exact fixedPC4006

@[simp] theorem earlyExtraPC2938 : Artifact.submissionArtifact.instructionPC 3307 = 4352 := by
  exact fixedPC4007

@[simp] theorem earlyExtraPC2939 : Artifact.submissionArtifact.instructionPC 3308 = 4353 := by
  exact fixedPC4008

@[simp] theorem earlyExtraPC2940 : Artifact.submissionArtifact.instructionPC 3309 = 4354 := by
  exact fixedPC4009

@[simp] theorem earlyExtraPC2941 : Artifact.submissionArtifact.instructionPC 3310 = 4357 := by
  exact fixedPC4010

@[simp] theorem earlyExtraPC2942 : Artifact.submissionArtifact.instructionPC 3311 = 4358 := by
  exact fixedPC4011

@[simp] theorem earlyExtraPC2943 : Artifact.submissionArtifact.instructionPC 3312 = 4361 := by
  exact fixedPC4012

@[simp] theorem earlyExtraPC3918 : Artifact.submissionArtifact.instructionPC 3613 = 4767 := by
  calc
    Artifact.submissionArtifact.instructionPC 3613 =
        Artifact.submissionArtifact.instructionPC 3612 + ((.push 2 319) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3612 (.push 2 319) (by rfl)
    _ = 4767 := by rw [fixedPC3948]; rfl

@[simp] theorem earlyExtraPC3919 : Artifact.submissionArtifact.instructionPC 3614 = 4768 := by
  calc
    Artifact.submissionArtifact.instructionPC 3614 =
        Artifact.submissionArtifact.instructionPC 3613 + ((.op .NOT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3613 (.op .NOT) (by rfl)
    _ = 4768 := by rw [earlyExtraPC3918]; rfl

@[simp] theorem earlyExtraPC3920 : Artifact.submissionArtifact.instructionPC 3615 = 4771 := by
  calc
    Artifact.submissionArtifact.instructionPC 3615 =
        Artifact.submissionArtifact.instructionPC 3614 + ((.push 2 4772) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3614 (.push 2 4772) (by rfl)
    _ = 4771 := by rw [earlyExtraPC3919]; rfl


end Challenge.Modexp.Submission.Proofs.Fast
