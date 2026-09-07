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
    [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD]

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
    (hhi : index ≤ 2763) :
    Artifact.submissionArtifact.instructionPC index =
            [4136, 4137, 4138, 4139, 4172, 4173, 4174, 4175, 4176, 4177, 4178, 4179, 4180, 4181,
       4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195,
       4196, 4197, 4198, 4199, 4200, 4233, 4234, 4235, 4236, 4269][index - firstStartIndex]! := by
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
    [firstOpAt 0 .JUMPDEST, firstOpAt 1 (.Dup ⟨0, by decide⟩), firstOpAt 2 .MLOAD,
   firstPushAt 3 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   firstOpAt 4 (.Dup ⟨5, by decide⟩), firstOpAt 5 (.Dup ⟨2, by decide⟩), firstOpAt 6 .MUL,
   firstOpAt 7 (.Swap ⟨1, by decide⟩), firstOpAt 8 (.Dup ⟨6, by decide⟩), firstOpAt 9 .MULMOD,
   firstOpAt 10 (.Dup ⟨1, by decide⟩), firstOpAt 11 (.Dup ⟨1, by decide⟩), firstOpAt 12 .LT,
   firstOpAt 13 .SUB, firstOpAt 14 (.Dup ⟨4, by decide⟩), firstOpAt 15 (.Dup ⟨2, by decide⟩),
   firstOpAt 16 .ADD, firstOpAt 17 (.Dup ⟨0, by decide⟩), firstOpAt 18 (.Swap ⟨5, by decide⟩),
   firstOpAt 19 .GT, firstOpAt 20 .SUB, firstOpAt 21 .SUB, firstOpAt 22 (.Dup ⟨3, by decide⟩),
   firstOpAt 23 (.Dup ⟨3, by decide⟩), firstOpAt 24 .MLOAD, firstOpAt 25 .ADD,
   firstOpAt 26 (.Dup ⟨0, by decide⟩), firstOpAt 27 (.Swap ⟨4, by decide⟩), firstOpAt 28 .GT,
   firstOpAt 29 .ADD, firstOpAt 30 (.Swap ⟨2, by decide⟩), firstOpAt 31 (.Dup ⟨2, by decide⟩),
   firstPushAt 32 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 33 .ADD, firstOpAt 34 (.Swap ⟨2, by decide⟩), firstOpAt 35 .MSTORE,
   firstPushAt 36 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 37 .ADD]
def middleOneStartIndex : Nat := 2764

private def middleOneTemplate : List Instr :=
    [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD]

private theorem middleOneSlice_eq :
    (Artifact.submissionInstructions.drop middleOneStartIndex).take
        middleOneTemplate.length = middleOneTemplate := by
  rfl

private theorem middleOneGetElem (offset : Nat)
    (hoffset : offset < middleOneTemplate.length) :
    Artifact.submissionInstructions[middleOneStartIndex + offset]? =
      middleOneTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) middleOneSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem middleOneStartPC :
    Artifact.submissionArtifact.instructionPC middleOneStartIndex = 4270 := by
  rfl

@[simp] theorem middleOnePC (index : Nat) (hlo : middleOneStartIndex ≤ index)
    (hhi : index ≤ 2800) :
    Artifact.submissionArtifact.instructionPC index =
            [4270, 4271, 4272, 4305, 4306, 4307, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315,
       4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329,
       4330, 4331, 4332, 4333, 4366, 4367, 4368, 4369, 4402][index - middleOneStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (middleOneStartIndex + (index - middleOneStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC middleOneStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop middleOneStartIndex).take
              (index - middleOneStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact middleOneStartIndex
        (index - middleOneStartIndex)
    _ = _ := by
      rw [middleOneStartPC]
      interval_cases index <;> rfl


def middleOneOpAt (offset : Nat) (op : Operation)
    (hget : middleOneTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < middleOneTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨middleOneStartIndex + offset, .op op, (middleOneGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def middleOnePushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : middleOneTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < middleOneTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨middleOneStartIndex + offset, .push width value,
    (middleOneGetElem offset hoffset).trans hget, hwf⟩

/-- MiddleOne MAC: instructions 2769..2810, pc 4270..4412. -/
def middleOneMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
    [middleOneOpAt 0 (.Dup ⟨0, by decide⟩), middleOneOpAt 1 .MLOAD,
   middleOnePushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   middleOneOpAt 3 (.Dup ⟨5, by decide⟩), middleOneOpAt 4 (.Dup ⟨2, by decide⟩),
   middleOneOpAt 5 .MUL, middleOneOpAt 6 (.Swap ⟨1, by decide⟩),
   middleOneOpAt 7 (.Dup ⟨6, by decide⟩), middleOneOpAt 8 .MULMOD,
   middleOneOpAt 9 (.Dup ⟨1, by decide⟩), middleOneOpAt 10 (.Dup ⟨1, by decide⟩),
   middleOneOpAt 11 .LT, middleOneOpAt 12 .SUB, middleOneOpAt 13 (.Dup ⟨4, by decide⟩),
   middleOneOpAt 14 (.Dup ⟨2, by decide⟩), middleOneOpAt 15 .ADD,
   middleOneOpAt 16 (.Dup ⟨0, by decide⟩), middleOneOpAt 17 (.Swap ⟨5, by decide⟩),
   middleOneOpAt 18 .GT, middleOneOpAt 19 .SUB, middleOneOpAt 20 .SUB,
   middleOneOpAt 21 (.Dup ⟨3, by decide⟩), middleOneOpAt 22 (.Dup ⟨3, by decide⟩),
   middleOneOpAt 23 .MLOAD, middleOneOpAt 24 .ADD, middleOneOpAt 25 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 26 (.Swap ⟨4, by decide⟩), middleOneOpAt 27 .GT, middleOneOpAt 28 .ADD,
   middleOneOpAt 29 (.Swap ⟨2, by decide⟩), middleOneOpAt 30 (.Dup ⟨2, by decide⟩),
   middleOnePushAt 31 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   middleOneOpAt 32 .ADD, middleOneOpAt 33 (.Swap ⟨2, by decide⟩), middleOneOpAt 34 .MSTORE,
   middleOnePushAt 35 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   middleOneOpAt 36 .ADD]
def middleTwoStartIndex : Nat := 2801

private def middleTwoTemplate : List Instr :=
    [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD]

private theorem middleTwoSlice_eq :
    (Artifact.submissionInstructions.drop middleTwoStartIndex).take
        middleTwoTemplate.length = middleTwoTemplate := by
  rfl

private theorem middleTwoGetElem (offset : Nat)
    (hoffset : offset < middleTwoTemplate.length) :
    Artifact.submissionInstructions[middleTwoStartIndex + offset]? =
      middleTwoTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) middleTwoSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem middleTwoStartPC :
    Artifact.submissionArtifact.instructionPC middleTwoStartIndex = 4403 := by
  rfl

@[simp] theorem middleTwoPC (index : Nat) (hlo : middleTwoStartIndex ≤ index)
    (hhi : index ≤ 2837) :
    Artifact.submissionArtifact.instructionPC index =
            [4403, 4404, 4405, 4438, 4439, 4440, 4441, 4442, 4443, 4444, 4445, 4446, 4447, 4448,
       4449, 4450, 4451, 4452, 4453, 4454, 4455, 4456, 4457, 4458, 4459, 4460, 4461, 4462,
       4463, 4464, 4465, 4466, 4499, 4500, 4501, 4502, 4535][index - middleTwoStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (middleTwoStartIndex + (index - middleTwoStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC middleTwoStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop middleTwoStartIndex).take
              (index - middleTwoStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact middleTwoStartIndex
        (index - middleTwoStartIndex)
    _ = _ := by
      rw [middleTwoStartPC]
      interval_cases index <;> rfl


def middleTwoOpAt (offset : Nat) (op : Operation)
    (hget : middleTwoTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < middleTwoTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨middleTwoStartIndex + offset, .op op, (middleTwoGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def middleTwoPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : middleTwoTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < middleTwoTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨middleTwoStartIndex + offset, .push width value,
    (middleTwoGetElem offset hoffset).trans hget, hwf⟩

/-- MiddleTwo MAC: instructions 2811..2852, pc 4403..4550. -/
def middleTwoMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
    [middleTwoOpAt 0 (.Dup ⟨0, by decide⟩), middleTwoOpAt 1 .MLOAD,
   middleTwoPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   middleTwoOpAt 3 (.Dup ⟨5, by decide⟩), middleTwoOpAt 4 (.Dup ⟨2, by decide⟩),
   middleTwoOpAt 5 .MUL, middleTwoOpAt 6 (.Swap ⟨1, by decide⟩),
   middleTwoOpAt 7 (.Dup ⟨6, by decide⟩), middleTwoOpAt 8 .MULMOD,
   middleTwoOpAt 9 (.Dup ⟨1, by decide⟩), middleTwoOpAt 10 (.Dup ⟨1, by decide⟩),
   middleTwoOpAt 11 .LT, middleTwoOpAt 12 .SUB, middleTwoOpAt 13 (.Dup ⟨4, by decide⟩),
   middleTwoOpAt 14 (.Dup ⟨2, by decide⟩), middleTwoOpAt 15 .ADD,
   middleTwoOpAt 16 (.Dup ⟨0, by decide⟩), middleTwoOpAt 17 (.Swap ⟨5, by decide⟩),
   middleTwoOpAt 18 .GT, middleTwoOpAt 19 .SUB, middleTwoOpAt 20 .SUB,
   middleTwoOpAt 21 (.Dup ⟨3, by decide⟩), middleTwoOpAt 22 (.Dup ⟨3, by decide⟩),
   middleTwoOpAt 23 .MLOAD, middleTwoOpAt 24 .ADD, middleTwoOpAt 25 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 26 (.Swap ⟨4, by decide⟩), middleTwoOpAt 27 .GT, middleTwoOpAt 28 .ADD,
   middleTwoOpAt 29 (.Swap ⟨2, by decide⟩), middleTwoOpAt 30 (.Dup ⟨2, by decide⟩),
   middleTwoPushAt 31 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   middleTwoOpAt 32 .ADD, middleTwoOpAt 33 (.Swap ⟨2, by decide⟩), middleTwoOpAt 34 .MSTORE,
   middleTwoPushAt 35 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   middleTwoOpAt 36 .ADD]
def secondStartIndex : Nat := 2838

private def secondTemplate : List Instr :=
    [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .push 2 4136,
   .op .JUMPI, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4536 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 2899) :
    Artifact.submissionArtifact.instructionPC index =
            [4536, 4537, 4538, 4571, 4572, 4573, 4574, 4575, 4576, 4577, 4578, 4579, 4580, 4581,
       4582, 4583, 4584, 4585, 4586, 4587, 4588, 4589, 4590, 4591, 4592, 4593, 4594, 4595,
       4596, 4597, 4598, 4599, 4632, 4633, 4634, 4635, 4668, 4669, 4670, 4671, 4672, 4675,
       4676, 4677, 4678, 4679, 4680, 4681, 4682, 4683, 4684, 4685, 4686, 4687, 4688, 4689,
       4690, 4691, 4692, 4693, 4694, 4695][index - secondStartIndex]! := by
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

/-- Second MAC: instructions 2853..2899, pc 4536..4695. -/
def secondMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
    [secondOpAt 0 (.Dup ⟨0, by decide⟩), secondOpAt 1 .MLOAD,
   secondPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   secondOpAt 3 (.Dup ⟨5, by decide⟩), secondOpAt 4 (.Dup ⟨2, by decide⟩), secondOpAt 5 .MUL,
   secondOpAt 6 (.Swap ⟨1, by decide⟩), secondOpAt 7 (.Dup ⟨6, by decide⟩),
   secondOpAt 8 .MULMOD, secondOpAt 9 (.Dup ⟨1, by decide⟩),
   secondOpAt 10 (.Dup ⟨1, by decide⟩), secondOpAt 11 .LT, secondOpAt 12 .SUB,
   secondOpAt 13 (.Dup ⟨4, by decide⟩), secondOpAt 14 (.Dup ⟨2, by decide⟩),
   secondOpAt 15 .ADD, secondOpAt 16 (.Dup ⟨0, by decide⟩),
   secondOpAt 17 (.Swap ⟨5, by decide⟩), secondOpAt 18 .GT, secondOpAt 19 .SUB,
   secondOpAt 20 .SUB, secondOpAt 21 (.Dup ⟨3, by decide⟩),
   secondOpAt 22 (.Dup ⟨3, by decide⟩), secondOpAt 23 .MLOAD, secondOpAt 24 .ADD,
   secondOpAt 25 (.Dup ⟨0, by decide⟩), secondOpAt 26 (.Swap ⟨4, by decide⟩),
   secondOpAt 27 .GT, secondOpAt 28 .ADD, secondOpAt 29 (.Swap ⟨2, by decide⟩),
   secondOpAt 30 (.Dup ⟨2, by decide⟩),
   secondPushAt 31 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 32 .ADD, secondOpAt 33 (.Swap ⟨2, by decide⟩), secondOpAt 34 .MSTORE,
   secondPushAt 35 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 36 .ADD, secondOpAt 37 (.Dup ⟨5, by decide⟩),
   secondOpAt 38 (.Dup ⟨1, by decide⟩), secondOpAt 39 .GT, secondPushAt 40 2 4136,
   secondOpAt 41 .JUMPI]

/-- Same trace plus the padding `JUMPDEST`s on the fall-through path. -/
def secondMacExit :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  secondMac ++
  [secondOpAt 42 .JUMPDEST,
   secondOpAt 43 .JUMPDEST,
   secondOpAt 44 .JUMPDEST,
   secondOpAt 45 .JUMPDEST,
   secondOpAt 46 .JUMPDEST,
   secondOpAt 47 .JUMPDEST,
   secondOpAt 48 .JUMPDEST,
   secondOpAt 49 .JUMPDEST,
   secondOpAt 50 .JUMPDEST,
   secondOpAt 51 .JUMPDEST,
   secondOpAt 52 .JUMPDEST,
   secondOpAt 53 .JUMPDEST,
   secondOpAt 54 .JUMPDEST,
   secondOpAt 55 .JUMPDEST,
   secondOpAt 56 .JUMPDEST,
   secondOpAt 57 .JUMPDEST,
   secondOpAt 58 .JUMPDEST,
   secondOpAt 59 .JUMPDEST,
   secondOpAt 60 .JUMPDEST,
   secondOpAt 61 .JUMPDEST]


/-- The complete four-MAC L1 block, retained for whole-block consumers. -/
def cios2L1 := firstMac ++ middleOneMac ++ middleTwoMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
