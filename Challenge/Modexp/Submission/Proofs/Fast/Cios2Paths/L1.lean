import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

def firstStartIndex : Nat := 2726

private def firstTemplate : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

private theorem firstSlice_eq :
    (Artifact.submissionInstructions.drop firstStartIndex).take
        firstTemplate.length = firstTemplate := by
  rfl

private theorem firstGetElem (offset : Nat)
    (hoffset : offset < firstTemplate.length) :
    Artifact.submissionInstructions[firstStartIndex + offset]? =
      firstTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) firstSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem firstStartPC :
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4136 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 2768) :
    Artifact.submissionArtifact.instructionPC index =
      [4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4177, 4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4197, 4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4238, 4239, 4240, 4273, 4274][index - firstStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (firstStartIndex + (index - firstStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC firstStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop firstStartIndex).take
              (index - firstStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact firstStartIndex
        (index - firstStartIndex)
    _ = _ := by
      rw [firstStartPC]
      interval_cases index <;> rfl

def firstOpAt (offset : Nat) (op : Operation)
    (hget : firstTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < firstTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨firstStartIndex + offset, .op op, (firstGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def firstPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : firstTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < firstTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨firstStartIndex + offset, .push width value,
    (firstGetElem offset hoffset).trans hget, hwf⟩

/-- Live instructions 2726..2768, pc 4136..4274. -/
def firstMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [firstOpAt 0 .JUMPDEST,
   firstOpAt 1 (.Dup ⟨3, by decide⟩),
   firstOpAt 2 (.Dup ⟨1, by decide⟩),
   firstOpAt 3 .MLOAD,
   firstOpAt 4 (.Dup ⟨1, by decide⟩),
   firstOpAt 5 (.Dup ⟨1, by decide⟩),
   firstOpAt 6 .MUL,
   firstOpAt 7 (.Swap ⟨1, by decide⟩),
   firstPushAt 8 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   firstOpAt 9 (.Swap ⟨1, by decide⟩),
   firstOpAt 10 .MULMOD,
   firstOpAt 11 (.Dup ⟨1, by decide⟩),
   firstOpAt 12 (.Dup ⟨1, by decide⟩),
   firstOpAt 13 .LT,
   firstOpAt 14 (.Dup ⟨2, by decide⟩),
   firstOpAt 15 .ADD,
   firstOpAt 16 (.Swap ⟨0, by decide⟩),
   firstOpAt 17 .SUB,
   firstOpAt 18 (.Dup ⟨3, by decide⟩),
   firstOpAt 19 .MLOAD,
   firstOpAt 20 (.Swap ⟨1, by decide⟩),
   firstOpAt 21 (.Dup ⟨2, by decide⟩),
   firstOpAt 22 .ADD,
   firstOpAt 23 (.Swap ⟨1, by decide⟩),
   firstOpAt 24 (.Dup ⟨2, by decide⟩),
   firstOpAt 25 .LT,
   firstOpAt 26 .ADD,
   firstOpAt 27 (.Swap ⟨0, by decide⟩),
   firstOpAt 28 (.Dup ⟨4, by decide⟩),
   firstOpAt 29 .ADD,
   firstOpAt 30 (.Swap ⟨3, by decide⟩),
   firstOpAt 31 (.Dup ⟨4, by decide⟩),
   firstOpAt 32 .LT,
   firstOpAt 33 .ADD,
   firstOpAt 34 (.Swap ⟨2, by decide⟩),
   firstOpAt 35 (.Dup ⟨2, by decide⟩),
   firstOpAt 36 .MSTORE,
   firstPushAt 37 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 38 .ADD,
   firstOpAt 39 (.Swap ⟨0, by decide⟩),
   firstPushAt 40 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 41 .ADD,
   firstOpAt 42 (.Swap ⟨0, by decide⟩)]

def secondStartIndex : Nat := 2769

private def secondTemplate : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

private theorem secondSlice_eq :
    (Artifact.submissionInstructions.drop secondStartIndex).take
        secondTemplate.length = secondTemplate := by
  rfl

private theorem secondGetElem (offset : Nat)
    (hoffset : offset < secondTemplate.length) :
    Artifact.submissionInstructions[secondStartIndex + offset]? =
      secondTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) secondSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem secondStartPC :
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4275 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 2810) :
    Artifact.submissionArtifact.instructionPC index =
      [4275, 4276, 4277, 4278, 4279, 4280, 4281, 4282, 4315, 4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336, 4337, 4338, 4339, 4340, 4341, 4342, 4343, 4376, 4377, 4378, 4411, 4412][index - secondStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (secondStartIndex + (index - secondStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC secondStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop secondStartIndex).take
              (index - secondStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact secondStartIndex
        (index - secondStartIndex)
    _ = _ := by
      rw [secondStartPC]
      interval_cases index <;> rfl

def secondOpAt (offset : Nat) (op : Operation)
    (hget : secondTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < secondTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨secondStartIndex + offset, .op op, (secondGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def secondPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : secondTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < secondTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨secondStartIndex + offset, .push width value,
    (secondGetElem offset hoffset).trans hget, hwf⟩

/-- Live instructions 2769..2810, pc 4275..4412. -/
def secondMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [secondOpAt 0 (.Dup ⟨3, by decide⟩),
   secondOpAt 1 (.Dup ⟨1, by decide⟩),
   secondOpAt 2 .MLOAD,
   secondOpAt 3 (.Dup ⟨1, by decide⟩),
   secondOpAt 4 (.Dup ⟨1, by decide⟩),
   secondOpAt 5 .MUL,
   secondOpAt 6 (.Swap ⟨1, by decide⟩),
   secondPushAt 7 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   secondOpAt 8 (.Swap ⟨1, by decide⟩),
   secondOpAt 9 .MULMOD,
   secondOpAt 10 (.Dup ⟨1, by decide⟩),
   secondOpAt 11 (.Dup ⟨1, by decide⟩),
   secondOpAt 12 .LT,
   secondOpAt 13 (.Dup ⟨2, by decide⟩),
   secondOpAt 14 .ADD,
   secondOpAt 15 (.Swap ⟨0, by decide⟩),
   secondOpAt 16 .SUB,
   secondOpAt 17 (.Dup ⟨3, by decide⟩),
   secondOpAt 18 .MLOAD,
   secondOpAt 19 (.Swap ⟨1, by decide⟩),
   secondOpAt 20 (.Dup ⟨2, by decide⟩),
   secondOpAt 21 .ADD,
   secondOpAt 22 (.Swap ⟨1, by decide⟩),
   secondOpAt 23 (.Dup ⟨2, by decide⟩),
   secondOpAt 24 .LT,
   secondOpAt 25 .ADD,
   secondOpAt 26 (.Swap ⟨0, by decide⟩),
   secondOpAt 27 (.Dup ⟨4, by decide⟩),
   secondOpAt 28 .ADD,
   secondOpAt 29 (.Swap ⟨3, by decide⟩),
   secondOpAt 30 (.Dup ⟨4, by decide⟩),
   secondOpAt 31 .LT,
   secondOpAt 32 .ADD,
   secondOpAt 33 (.Swap ⟨2, by decide⟩),
   secondOpAt 34 (.Dup ⟨2, by decide⟩),
   secondOpAt 35 .MSTORE,
   secondPushAt 36 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 37 .ADD,
   secondOpAt 38 (.Swap ⟨0, by decide⟩),
   secondPushAt 39 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 40 .ADD,
   secondOpAt 41 (.Swap ⟨0, by decide⟩)]

def thirdStartIndex : Nat := 2811

private def thirdTemplate : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

private theorem thirdSlice_eq :
    (Artifact.submissionInstructions.drop thirdStartIndex).take
        thirdTemplate.length = thirdTemplate := by
  rfl

private theorem thirdGetElem (offset : Nat)
    (hoffset : offset < thirdTemplate.length) :
    Artifact.submissionInstructions[thirdStartIndex + offset]? =
      thirdTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) thirdSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem thirdStartPC :
    Artifact.submissionArtifact.instructionPC thirdStartIndex = 4413 := by
  rfl

@[simp] theorem thirdPC (index : Nat) (hlo : thirdStartIndex ≤ index)
    (hhi : index ≤ 2852) :
    Artifact.submissionArtifact.instructionPC index =
      [4413, 4414, 4415, 4416, 4417, 4418, 4419, 4420, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462, 4463, 4464, 4465, 4466, 4467, 4468, 4469, 4470, 4471, 4472, 4473, 4474, 4475, 4476, 4477, 4478, 4479, 4480, 4481, 4514, 4515, 4516, 4549, 4550][index - thirdStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (thirdStartIndex + (index - thirdStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC thirdStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop thirdStartIndex).take
              (index - thirdStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact thirdStartIndex
        (index - thirdStartIndex)
    _ = _ := by
      rw [thirdStartPC]
      interval_cases index <;> rfl

def thirdOpAt (offset : Nat) (op : Operation)
    (hget : thirdTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < thirdTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨thirdStartIndex + offset, .op op, (thirdGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def thirdPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : thirdTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < thirdTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨thirdStartIndex + offset, .push width value,
    (thirdGetElem offset hoffset).trans hget, hwf⟩

/-- Live instructions 2811..2852, pc 4413..4550. -/
def thirdMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [thirdOpAt 0 (.Dup ⟨3, by decide⟩),
   thirdOpAt 1 (.Dup ⟨1, by decide⟩),
   thirdOpAt 2 .MLOAD,
   thirdOpAt 3 (.Dup ⟨1, by decide⟩),
   thirdOpAt 4 (.Dup ⟨1, by decide⟩),
   thirdOpAt 5 .MUL,
   thirdOpAt 6 (.Swap ⟨1, by decide⟩),
   thirdPushAt 7 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   thirdOpAt 8 (.Swap ⟨1, by decide⟩),
   thirdOpAt 9 .MULMOD,
   thirdOpAt 10 (.Dup ⟨1, by decide⟩),
   thirdOpAt 11 (.Dup ⟨1, by decide⟩),
   thirdOpAt 12 .LT,
   thirdOpAt 13 (.Dup ⟨2, by decide⟩),
   thirdOpAt 14 .ADD,
   thirdOpAt 15 (.Swap ⟨0, by decide⟩),
   thirdOpAt 16 .SUB,
   thirdOpAt 17 (.Dup ⟨3, by decide⟩),
   thirdOpAt 18 .MLOAD,
   thirdOpAt 19 (.Swap ⟨1, by decide⟩),
   thirdOpAt 20 (.Dup ⟨2, by decide⟩),
   thirdOpAt 21 .ADD,
   thirdOpAt 22 (.Swap ⟨1, by decide⟩),
   thirdOpAt 23 (.Dup ⟨2, by decide⟩),
   thirdOpAt 24 .LT,
   thirdOpAt 25 .ADD,
   thirdOpAt 26 (.Swap ⟨0, by decide⟩),
   thirdOpAt 27 (.Dup ⟨4, by decide⟩),
   thirdOpAt 28 .ADD,
   thirdOpAt 29 (.Swap ⟨3, by decide⟩),
   thirdOpAt 30 (.Dup ⟨4, by decide⟩),
   thirdOpAt 31 .LT,
   thirdOpAt 32 .ADD,
   thirdOpAt 33 (.Swap ⟨2, by decide⟩),
   thirdOpAt 34 (.Dup ⟨2, by decide⟩),
   thirdOpAt 35 .MSTORE,
   thirdPushAt 36 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   thirdOpAt 37 .ADD,
   thirdOpAt 38 (.Swap ⟨0, by decide⟩),
   thirdPushAt 39 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   thirdOpAt 40 .ADD,
   thirdOpAt 41 (.Swap ⟨0, by decide⟩)]

def fourthStartIndex : Nat := 2853

private def fourthTemplate : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4136,
   .op .JUMPI]

private theorem fourthSlice_eq :
    (Artifact.submissionInstructions.drop fourthStartIndex).take
        fourthTemplate.length = fourthTemplate := by
  rfl

private theorem fourthGetElem (offset : Nat)
    (hoffset : offset < fourthTemplate.length) :
    Artifact.submissionInstructions[fourthStartIndex + offset]? =
      fourthTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) fourthSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem fourthStartPC :
    Artifact.submissionArtifact.instructionPC fourthStartIndex = 4551 := by
  rfl

@[simp] theorem fourthPC (index : Nat) (hlo : fourthStartIndex ≤ index)
    (hhi : index ≤ 2899) :
    Artifact.submissionArtifact.instructionPC index =
      [4551, 4552, 4553, 4554, 4555, 4556, 4557, 4558, 4591, 4592, 4593, 4594, 4595, 4596, 4597, 4598, 4599, 4600, 4601, 4602, 4603, 4604, 4605, 4606, 4607, 4608, 4609, 4610, 4611, 4612, 4613, 4614, 4615, 4616, 4617, 4618, 4619, 4652, 4653, 4654, 4687, 4688, 4689, 4690, 4691, 4692, 4695][index - fourthStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (fourthStartIndex + (index - fourthStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC fourthStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop fourthStartIndex).take
              (index - fourthStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact fourthStartIndex
        (index - fourthStartIndex)
    _ = _ := by
      rw [fourthStartPC]
      interval_cases index <;> rfl

def fourthOpAt (offset : Nat) (op : Operation)
    (hget : fourthTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < fourthTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨fourthStartIndex + offset, .op op, (fourthGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def fourthPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : fourthTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < fourthTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨fourthStartIndex + offset, .push width value,
    (fourthGetElem offset hoffset).trans hget, hwf⟩

/-- Live instructions 2853..2899, pc 4551..4695. -/
def fourthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fourthOpAt 0 (.Dup ⟨3, by decide⟩),
   fourthOpAt 1 (.Dup ⟨1, by decide⟩),
   fourthOpAt 2 .MLOAD,
   fourthOpAt 3 (.Dup ⟨1, by decide⟩),
   fourthOpAt 4 (.Dup ⟨1, by decide⟩),
   fourthOpAt 5 .MUL,
   fourthOpAt 6 (.Swap ⟨1, by decide⟩),
   fourthPushAt 7 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   fourthOpAt 8 (.Swap ⟨1, by decide⟩),
   fourthOpAt 9 .MULMOD,
   fourthOpAt 10 (.Dup ⟨1, by decide⟩),
   fourthOpAt 11 (.Dup ⟨1, by decide⟩),
   fourthOpAt 12 .LT,
   fourthOpAt 13 (.Dup ⟨2, by decide⟩),
   fourthOpAt 14 .ADD,
   fourthOpAt 15 (.Swap ⟨0, by decide⟩),
   fourthOpAt 16 .SUB,
   fourthOpAt 17 (.Dup ⟨3, by decide⟩),
   fourthOpAt 18 .MLOAD,
   fourthOpAt 19 (.Swap ⟨1, by decide⟩),
   fourthOpAt 20 (.Dup ⟨2, by decide⟩),
   fourthOpAt 21 .ADD,
   fourthOpAt 22 (.Swap ⟨1, by decide⟩),
   fourthOpAt 23 (.Dup ⟨2, by decide⟩),
   fourthOpAt 24 .LT,
   fourthOpAt 25 .ADD,
   fourthOpAt 26 (.Swap ⟨0, by decide⟩),
   fourthOpAt 27 (.Dup ⟨4, by decide⟩),
   fourthOpAt 28 .ADD,
   fourthOpAt 29 (.Swap ⟨3, by decide⟩),
   fourthOpAt 30 (.Dup ⟨4, by decide⟩),
   fourthOpAt 31 .LT,
   fourthOpAt 32 .ADD,
   fourthOpAt 33 (.Swap ⟨2, by decide⟩),
   fourthOpAt 34 (.Dup ⟨2, by decide⟩),
   fourthOpAt 35 .MSTORE,
   fourthPushAt 36 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   fourthOpAt 37 .ADD,
   fourthOpAt 38 (.Swap ⟨0, by decide⟩),
   fourthPushAt 39 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   fourthOpAt 40 .ADD,
   fourthOpAt 41 (.Swap ⟨0, by decide⟩),
   fourthOpAt 42 (.Dup ⟨5, by decide⟩),
   fourthOpAt 43 (.Dup ⟨1, by decide⟩),
   fourthOpAt 44 .GT,
   fourthPushAt 45 2 4136,
   fourthOpAt 46 .JUMPI]

def cios2L1 := firstMac ++ secondMac ++ thirdMac ++ fourthMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
