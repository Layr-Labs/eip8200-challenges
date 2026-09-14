import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixedPC3
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

@[simp] theorem fixedPC3938 : Artifact.submissionArtifact.instructionPC 3602 = 4750 := by
  calc
    Artifact.submissionArtifact.instructionPC 3602 =
        Artifact.submissionArtifact.instructionPC 3601 + ((.op .SUB) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3601 (.op .SUB) (by rfl)
    _ = 4750 := by rw [fixedPC3937]; rfl

@[simp] theorem fixedPC3939 : Artifact.submissionArtifact.instructionPC 3603 = 4751 := by
  calc
    Artifact.submissionArtifact.instructionPC 3603 =
        Artifact.submissionArtifact.instructionPC 3602 + ((.op (.Swap ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3602 (.op (.Swap ⟨2, by decide⟩)) (by rfl)
    _ = 4751 := by rw [fixedPC3938]; rfl

@[simp] theorem fixedPC3940 : Artifact.submissionArtifact.instructionPC 3604 = 4752 := by
  calc
    Artifact.submissionArtifact.instructionPC 3604 =
        Artifact.submissionArtifact.instructionPC 3603 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3603 (.op .GT) (by rfl)
    _ = 4752 := by rw [fixedPC3939]; rfl

@[simp] theorem fixedPC3941 : Artifact.submissionArtifact.instructionPC 3605 = 4753 := by
  calc
    Artifact.submissionArtifact.instructionPC 3605 =
        Artifact.submissionArtifact.instructionPC 3604 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3604 (.op .OR) (by rfl)
    _ = 4753 := by rw [fixedPC3940]; rfl

@[simp] theorem fixedPC3942 : Artifact.submissionArtifact.instructionPC 3606 = 4754 := by
  calc
    Artifact.submissionArtifact.instructionPC 3606 =
        Artifact.submissionArtifact.instructionPC 3605 + ((.op (.Swap ⟨0, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3605 (.op (.Swap ⟨0, by decide⟩)) (by rfl)
    _ = 4754 := by rw [fixedPC3941]; rfl

@[simp] theorem fixedPC3943 : Artifact.submissionArtifact.instructionPC 3607 = 4757 := by
  calc
    Artifact.submissionArtifact.instructionPC 3607 =
        Artifact.submissionArtifact.instructionPC 3606 + ((.push 2 1792) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3606 (.push 2 1792) (by rfl)
    _ = 4757 := by rw [fixedPC3942]; rfl

@[simp] theorem fixedPC3944 : Artifact.submissionArtifact.instructionPC 3608 = 4758 := by
  calc
    Artifact.submissionArtifact.instructionPC 3608 =
        Artifact.submissionArtifact.instructionPC 3607 + ((.op .MSTORE) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3607 (.op .MSTORE) (by rfl)
    _ = 4758 := by rw [fixedPC3943]; rfl

@[simp] theorem fixedPC3945 : Artifact.submissionArtifact.instructionPC 3609 = 4759 := by
  calc
    Artifact.submissionArtifact.instructionPC 3609 =
        Artifact.submissionArtifact.instructionPC 3608 + ((.op .ISZERO) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3608 (.op .ISZERO) (by rfl)
    _ = 4759 := by rw [fixedPC3944]; rfl

@[simp] theorem fixedPC3946 : Artifact.submissionArtifact.instructionPC 3610 = 4762 := by
  calc
    Artifact.submissionArtifact.instructionPC 3610 =
        Artifact.submissionArtifact.instructionPC 3609 + ((.push 2 2080) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3609 (.push 2 2080) (by rfl)
    _ = 4762 := by rw [fixedPC3945]; rfl

@[simp] theorem fixedPC3947 : Artifact.submissionArtifact.instructionPC 3611 = 4763 := by
  calc
    Artifact.submissionArtifact.instructionPC 3611 =
        Artifact.submissionArtifact.instructionPC 3610 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3610 (.op .MLOAD) (by rfl)
    _ = 4763 := by rw [fixedPC3946]; rfl

@[simp] theorem fixedPC3948 : Artifact.submissionArtifact.instructionPC 3612 = 4764 := by
  calc
    Artifact.submissionArtifact.instructionPC 3612 =
        Artifact.submissionArtifact.instructionPC 3611 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3611 (.op .OR) (by rfl)
    _ = 4764 := by rw [fixedPC3947]; rfl

@[simp] theorem fixedPC3949 : Artifact.submissionArtifact.instructionPC 3617 = 4773 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3950 : Artifact.submissionArtifact.instructionPC 3617 = 4773 :=
  fixedPC3949

@[simp] theorem fixedPC3951 : Artifact.submissionArtifact.instructionPC 3618 = 4774 := by
  calc
    Artifact.submissionArtifact.instructionPC 3618 =
        Artifact.submissionArtifact.instructionPC 3617 + ((.op .MUL) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3617 (.op .MUL) (by rfl)
    _ = 4774 := by rw [fixedPC3949]; rfl

@[simp] theorem fixedPC3952 : Artifact.submissionArtifact.instructionPC 3619 = 4777 := by
  calc
    Artifact.submissionArtifact.instructionPC 3619 =
        Artifact.submissionArtifact.instructionPC 3618 + ((.push 2 2112) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3618 (.push 2 2112) (by rfl)
    _ = 4777 := by rw [fixedPC3951]; rfl

@[simp] theorem fixedPC3953 : Artifact.submissionArtifact.instructionPC 3620 = 4778 := by
  calc
    Artifact.submissionArtifact.instructionPC 3620 =
        Artifact.submissionArtifact.instructionPC 3619 + ((.op .ADD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3619 (.op .ADD) (by rfl)
    _ = 4778 := by rw [fixedPC3952]; rfl

@[simp] theorem fixedPC3954 : Artifact.submissionArtifact.instructionPC 3621 = 4781 := by
  calc
    Artifact.submissionArtifact.instructionPC 3621 =
        Artifact.submissionArtifact.instructionPC 3620 + ((.push 2 2688) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3620 (.push 2 2688) (by rfl)
    _ = 4781 := by rw [fixedPC3953]; rfl

@[simp] theorem fixedPC3955 : Artifact.submissionArtifact.instructionPC 3622 = 4782 := by
  calc
    Artifact.submissionArtifact.instructionPC 3622 =
        Artifact.submissionArtifact.instructionPC 3621 + ((.op .MLOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3621 (.op .MLOAD) (by rfl)
    _ = 4782 := by rw [fixedPC3954]; rfl

@[simp] theorem fixedPC3956 : Artifact.submissionArtifact.instructionPC 3623 = 4783 := by
  calc
    Artifact.submissionArtifact.instructionPC 3623 =
        Artifact.submissionArtifact.instructionPC 3622 + ((.op (.Swap ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3622 (.op (.Swap ⟨1, by decide⟩)) (by rfl)
    _ = 4783 := by rw [fixedPC3955]; rfl

@[simp] theorem fixedPC3957 : Artifact.submissionArtifact.instructionPC 3624 = 4784 := by
  calc
    Artifact.submissionArtifact.instructionPC 3624 =
        Artifact.submissionArtifact.instructionPC 3623 + ((.op .MCOPY) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3623 (.op .MCOPY) (by rfl)
    _ = 4784 := by rw [fixedPC3956]; rfl

@[simp] theorem fixedPC3958 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3959 : Artifact.submissionArtifact.instructionPC 0 = 0 := by
  exact fixedPC3958

@[simp] theorem fixedPC3960 : Artifact.submissionArtifact.instructionPC 1 = 1 := by
  calc
    Artifact.submissionArtifact.instructionPC 1 =
        Artifact.submissionArtifact.instructionPC 0 + ((.push 0 0) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 0 (.push 0 0) (by rfl)
    _ = 1 := by rw [fixedPC3959]; rfl

@[simp] theorem fixedPC3961 : Artifact.submissionArtifact.instructionPC 2 = 2 := by
  calc
    Artifact.submissionArtifact.instructionPC 2 =
        Artifact.submissionArtifact.instructionPC 1 + ((.op .CALLDATALOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 1 (.op .CALLDATALOAD) (by rfl)
    _ = 2 := by rw [fixedPC3960]; rfl

@[simp] theorem fixedPC3962 : Artifact.submissionArtifact.instructionPC 3 = 4 := by
  calc
    Artifact.submissionArtifact.instructionPC 3 =
        Artifact.submissionArtifact.instructionPC 2 + ((.push 1 32) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 2 (.push 1 32) (by rfl)
    _ = 4 := by rw [fixedPC3961]; rfl

@[simp] theorem fixedPC3963 : Artifact.submissionArtifact.instructionPC 4 = 5 := by
  calc
    Artifact.submissionArtifact.instructionPC 4 =
        Artifact.submissionArtifact.instructionPC 3 + ((.op .CALLDATALOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 3 (.op .CALLDATALOAD) (by rfl)
    _ = 5 := by rw [fixedPC3962]; rfl

@[simp] theorem fixedPC3964 : Artifact.submissionArtifact.instructionPC 5 = 7 := by
  calc
    Artifact.submissionArtifact.instructionPC 5 =
        Artifact.submissionArtifact.instructionPC 4 + ((.push 1 64) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 4 (.push 1 64) (by rfl)
    _ = 7 := by rw [fixedPC3963]; rfl

@[simp] theorem fixedPC3965 : Artifact.submissionArtifact.instructionPC 6 = 8 := by
  calc
    Artifact.submissionArtifact.instructionPC 6 =
        Artifact.submissionArtifact.instructionPC 5 + ((.op .CALLDATALOAD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 5 (.op .CALLDATALOAD) (by rfl)
    _ = 8 := by rw [fixedPC3964]; rfl

@[simp] theorem fixedPC3966 : Artifact.submissionArtifact.instructionPC 7 = 10 := by
  calc
    Artifact.submissionArtifact.instructionPC 7 =
        Artifact.submissionArtifact.instructionPC 6 + ((.push 1 32) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 6 (.push 1 32) (by rfl)
    _ = 10 := by rw [fixedPC3965]; rfl

@[simp] theorem fixedPC3967 : Artifact.submissionArtifact.instructionPC 8 = 11 := by
  calc
    Artifact.submissionArtifact.instructionPC 8 =
        Artifact.submissionArtifact.instructionPC 7 + ((.op (.Dup ⟨3, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 7 (.op (.Dup ⟨3, by decide⟩)) (by rfl)
    _ = 11 := by rw [fixedPC3966]; rfl

@[simp] theorem fixedPC3968 : Artifact.submissionArtifact.instructionPC 9 = 12 := by
  calc
    Artifact.submissionArtifact.instructionPC 9 =
        Artifact.submissionArtifact.instructionPC 8 + ((.op .GT) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 8 (.op .GT) (by rfl)
    _ = 12 := by rw [fixedPC3967]; rfl

@[simp] theorem fixedPC3969 : Artifact.submissionArtifact.instructionPC 10 = 13 := by
  calc
    Artifact.submissionArtifact.instructionPC 10 =
        Artifact.submissionArtifact.instructionPC 9 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 9 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 13 := by rw [fixedPC3968]; rfl

@[simp] theorem fixedPC3970 : Artifact.submissionArtifact.instructionPC 11 = 15 := by
  calc
    Artifact.submissionArtifact.instructionPC 11 =
        Artifact.submissionArtifact.instructionPC 10 + ((.push 1 32) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 10 (.push 1 32) (by rfl)
    _ = 15 := by rw [fixedPC3969]; rfl

@[simp] theorem fixedPC3971 : Artifact.submissionArtifact.instructionPC 12 = 16 := by
  calc
    Artifact.submissionArtifact.instructionPC 12 =
        Artifact.submissionArtifact.instructionPC 11 + ((.op .XOR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 11 (.op .XOR) (by rfl)
    _ = 16 := by rw [fixedPC3970]; rfl

@[simp] theorem fixedPC3972 : Artifact.submissionArtifact.instructionPC 13 = 17 := by
  calc
    Artifact.submissionArtifact.instructionPC 13 =
        Artifact.submissionArtifact.instructionPC 12 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 12 (.op .OR) (by rfl)
    _ = 17 := by rw [fixedPC3971]; rfl

@[simp] theorem fixedPC3973 : Artifact.submissionArtifact.instructionPC 14 = 18 := by
  calc
    Artifact.submissionArtifact.instructionPC 14 =
        Artifact.submissionArtifact.instructionPC 13 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 13 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 18 := by rw [fixedPC3972]; rfl

@[simp] theorem fixedPC3974 : Artifact.submissionArtifact.instructionPC 15 = 20 := by
  calc
    Artifact.submissionArtifact.instructionPC 15 =
        Artifact.submissionArtifact.instructionPC 14 + ((.push 1 32) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 14 (.push 1 32) (by rfl)
    _ = 20 := by rw [fixedPC3973]; rfl

@[simp] theorem fixedPC3975 : Artifact.submissionArtifact.instructionPC 16 = 21 := by
  calc
    Artifact.submissionArtifact.instructionPC 16 =
        Artifact.submissionArtifact.instructionPC 15 + ((.op .XOR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 15 (.op .XOR) (by rfl)
    _ = 21 := by rw [fixedPC3974]; rfl

@[simp] theorem fixedPC3976 : Artifact.submissionArtifact.instructionPC 17 = 22 := by
  calc
    Artifact.submissionArtifact.instructionPC 17 =
        Artifact.submissionArtifact.instructionPC 16 + ((.op .OR) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 16 (.op .OR) (by rfl)
    _ = 22 := by rw [fixedPC3975]; rfl

@[simp] theorem fixedPC3977 : Artifact.submissionArtifact.instructionPC 18 = 24 := by
  calc
    Artifact.submissionArtifact.instructionPC 18 =
        Artifact.submissionArtifact.instructionPC 17 + ((.push 1 126) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 17 (.push 1 126) (by rfl)
    _ = 24 := by rw [fixedPC3976]; rfl

@[simp] theorem fixedPC3978 : Artifact.submissionArtifact.instructionPC 20 = 26 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3979 : Artifact.submissionArtifact.instructionPC 21 = 27 := by
  calc
    Artifact.submissionArtifact.instructionPC 21 =
        Artifact.submissionArtifact.instructionPC 20 + ((.op (.Dup ⟨2, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 20 (.op (.Dup ⟨2, by decide⟩)) (by rfl)
    _ = 27 := by rw [fixedPC3978]; rfl

@[simp] theorem fixedPC3980 : Artifact.submissionArtifact.instructionPC 22 = 29 := by
  calc
    Artifact.submissionArtifact.instructionPC 22 =
        Artifact.submissionArtifact.instructionPC 21 + ((.push 1 96) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 21 (.push 1 96) (by rfl)
    _ = 29 := by rw [fixedPC3979]; rfl

@[simp] theorem fixedPC3981 : Artifact.submissionArtifact.instructionPC 26 = 34 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3982 : Artifact.submissionArtifact.instructionPC 31 = 39 := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  rfl

@[simp] theorem fixedPC3983 : Artifact.submissionArtifact.instructionPC 32 = 40 := by
  calc
    Artifact.submissionArtifact.instructionPC 32 =
        Artifact.submissionArtifact.instructionPC 31 + ((.op (.Dup ⟨1, by decide⟩)) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 31 (.op (.Dup ⟨1, by decide⟩)) (by rfl)
    _ = 40 := by rw [fixedPC3982]; rfl

@[simp] theorem fixedPC3984 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  calc
    Artifact.submissionArtifact.instructionPC 33 =
        Artifact.submissionArtifact.instructionPC 32 + ((.op .ADD) : Instr).bytes.length :=
      instructionPC_succ Artifact.submissionArtifact 32 (.op .ADD) (by rfl)
    _ = 41 := by rw [fixedPC3983]; rfl

@[simp] theorem fixedPC3985 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3984

@[simp] theorem fixedPC3986 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3985

@[simp] theorem fixedPC3987 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3986

@[simp] theorem fixedPC3988 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3987

@[simp] theorem fixedPC3989 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3988

@[simp] theorem fixedPC3990 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3989

@[simp] theorem fixedPC3991 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3990

@[simp] theorem fixedPC3992 : Artifact.submissionArtifact.instructionPC 33 = 41 := by
  exact fixedPC3991


end Challenge.Modexp.Submission.Proofs.Fast
