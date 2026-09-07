import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

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

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem firstStartPC :
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4136 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 2768) :
    Artifact.submissionArtifact.instructionPC index =
      [4136, 4137, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4177,
       4178, 4179, 4180, 4181, 4182, 4183, 4184, 4185, 4186, 4187,
       4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195, 4196, 4197,
       4198, 4199, 4200, 4201, 4202, 4203, 4204, 4205, 4238, 4239,
       4240, 4273, 4274][index - firstStartIndex]! := by
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

/-- First MAC: instructions 2726..2768, pc 4136..4274. -/
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
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4136,
   .op .JUMPI]

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
    (hhi : index ≤ 2815) :
    Artifact.submissionArtifact.instructionPC index =
      [4275, 4276, 4277, 4278, 4279, 4280, 4281, 4282, 4315, 4316,
       4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326,
       4327, 4328, 4329, 4330, 4331, 4332, 4333, 4334, 4335, 4336,
       4337, 4338, 4339, 4340, 4341, 4342, 4343, 4376, 4377, 4378,
       4411, 4412, 4413, 4414, 4415, 4416, 4419][index - secondStartIndex]! := by
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

/-- Second MAC and pair test: instructions 2769..2815, pc 4275..4419. -/
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
   secondOpAt 41 (.Swap ⟨0, by decide⟩),
   secondOpAt 42 (.Dup ⟨5, by decide⟩),
   secondOpAt 43 (.Dup ⟨1, by decide⟩),
   secondOpAt 44 .GT,
   secondPushAt 45 2 4136,
   secondOpAt 46 .JUMPI]

/-- The complete pair block, retained for whole-block consumers. -/
def cios2L1 := firstMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
