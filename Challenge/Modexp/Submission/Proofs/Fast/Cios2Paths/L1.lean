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

def firstStartIndex : Nat := 2622

private def firstTemplate : List Instr :=
  [
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 5 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 4 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD]

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
    (hhi : index ≤ 2662) :
    Artifact.submissionArtifact.instructionPC index =
      [4136,4137,4138,4139,4140,4141,4142,4143,4144,4145,4146,4147,4148,4149,4150,4151,4152,4153,4154,4155,4156,4157,4158,4159,4160,4161,4162,4163,4164,4165,4166,4167,4168,4169,4171,4172,4173,4174,4175,4177,4178][index - firstStartIndex]! := by
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

/-- First MAC: instructions 2726..2763, pc 4136..4178. -/
def firstMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [firstOpAt 0 .JUMPDEST,
   firstOpAt 1 (.Dup ⟨0, by decide⟩),
   firstOpAt 2 .MLOAD,
   firstPushAt 3 0 0,
   firstOpAt 4 .NOT,
   firstOpAt 5 (.Dup ⟨5, by decide⟩),
   firstOpAt 6 (.Dup ⟨2, by decide⟩),
   firstOpAt 7 .MUL,
   firstOpAt 8 (.Swap ⟨1, by decide⟩),
   firstOpAt 9 (.Dup ⟨6, by decide⟩),
   firstOpAt 10 .MULMOD,
   firstOpAt 11 (.Dup ⟨1, by decide⟩),
   firstOpAt 12 (.Dup ⟨1, by decide⟩),
   firstOpAt 13 .LT,
   firstOpAt 14 .SUB,
   firstOpAt 15 (.Dup ⟨4, by decide⟩),
   firstOpAt 16 (.Dup ⟨2, by decide⟩),
   firstOpAt 17 .ADD,
   firstOpAt 18 (.Dup ⟨0, by decide⟩),
   firstOpAt 19 (.Swap ⟨5, by decide⟩),
   firstOpAt 20 .GT,
   firstOpAt 21 .SUB,
   firstOpAt 22 .SUB,
   firstOpAt 23 (.Dup ⟨3, by decide⟩),
   firstOpAt 24 (.Dup ⟨3, by decide⟩),
   firstOpAt 25 .MLOAD,
   firstOpAt 26 .ADD,
   firstOpAt 27 (.Dup ⟨0, by decide⟩),
   firstOpAt 28 (.Swap ⟨4, by decide⟩),
   firstOpAt 29 .GT,
   firstOpAt 30 .ADD,
   firstOpAt 31 (.Swap ⟨2, by decide⟩),
   firstOpAt 32 (.Dup ⟨2, by decide⟩),
   firstPushAt 33 1 31,
   firstOpAt 34 .NOT,
   firstOpAt 35 .ADD,
   firstOpAt 36 (.Swap ⟨2, by decide⟩),
   firstOpAt 37 .MSTORE,
   firstPushAt 38 1 31,
   firstOpAt 39 .NOT,
   firstOpAt 40 .ADD]


def middleOneStartIndex : Nat := 2663

private def middleOneTemplate : List Instr :=
  [
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 5 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 4 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD]

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
    Artifact.submissionArtifact.instructionPC middleOneStartIndex = 4179 := by
  rfl

@[simp] theorem middleOnePC (index : Nat) (hlo : middleOneStartIndex ≤ index)
    (hhi : index ≤ 2702) :
    Artifact.submissionArtifact.instructionPC index =
      [4179,4180,4181,4182,4183,4184,4185,4186,4187,4188,4189,4190,4191,4192,4193,4194,4195,4196,4197,4198,4199,4200,4201,4202,4203,4204,4205,4206,4207,4208,4209,4210,4211,4213,4214,4215,4216,4217,4219,4220][index - middleOneStartIndex]! := by
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

/-- MiddleOne MAC: instructions 2764..2800, pc 4179..4220. -/
def middleOneMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [middleOneOpAt 0 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 1 .MLOAD,
   middleOnePushAt 2 0 0,
   middleOneOpAt 3 .NOT,
   middleOneOpAt 4 (.Dup ⟨5, by decide⟩),
   middleOneOpAt 5 (.Dup ⟨2, by decide⟩),
   middleOneOpAt 6 .MUL,
   middleOneOpAt 7 (.Swap ⟨1, by decide⟩),
   middleOneOpAt 8 (.Dup ⟨6, by decide⟩),
   middleOneOpAt 9 .MULMOD,
   middleOneOpAt 10 (.Dup ⟨1, by decide⟩),
   middleOneOpAt 11 (.Dup ⟨1, by decide⟩),
   middleOneOpAt 12 .LT,
   middleOneOpAt 13 .SUB,
   middleOneOpAt 14 (.Dup ⟨4, by decide⟩),
   middleOneOpAt 15 (.Dup ⟨2, by decide⟩),
   middleOneOpAt 16 .ADD,
   middleOneOpAt 17 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 18 (.Swap ⟨5, by decide⟩),
   middleOneOpAt 19 .GT,
   middleOneOpAt 20 .SUB,
   middleOneOpAt 21 .SUB,
   middleOneOpAt 22 (.Dup ⟨3, by decide⟩),
   middleOneOpAt 23 (.Dup ⟨3, by decide⟩),
   middleOneOpAt 24 .MLOAD,
   middleOneOpAt 25 .ADD,
   middleOneOpAt 26 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 27 (.Swap ⟨4, by decide⟩),
   middleOneOpAt 28 .GT,
   middleOneOpAt 29 .ADD,
   middleOneOpAt 30 (.Swap ⟨2, by decide⟩),
   middleOneOpAt 31 (.Dup ⟨2, by decide⟩),
   middleOnePushAt 32 1 31,
   middleOneOpAt 33 .NOT,
   middleOneOpAt 34 .ADD,
   middleOneOpAt 35 (.Swap ⟨2, by decide⟩),
   middleOneOpAt 36 .MSTORE,
   middleOnePushAt 37 1 31,
   middleOneOpAt 38 .NOT,
   middleOneOpAt 39 .ADD]


def middleTwoStartIndex : Nat := 2703

private def middleTwoTemplate : List Instr :=
  [
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 5 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 4 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD]

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
    Artifact.submissionArtifact.instructionPC middleTwoStartIndex = 4221 := by
  rfl

@[simp] theorem middleTwoPC (index : Nat) (hlo : middleTwoStartIndex ≤ index)
    (hhi : index ≤ 2742) :
    Artifact.submissionArtifact.instructionPC index =
      [4221,4222,4223,4224,4225,4226,4227,4228,4229,4230,4231,4232,4233,4234,4235,4236,4237,4238,4239,4240,4241,4242,4243,4244,4245,4246,4247,4248,4249,4250,4251,4252,4253,4255,4256,4257,4258,4259,4261,4262][index - middleTwoStartIndex]! := by
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

/-- MiddleTwo MAC: instructions 2801..2837, pc 4221..4262. -/
def middleTwoMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [middleTwoOpAt 0 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 1 .MLOAD,
   middleTwoPushAt 2 0 0,
   middleTwoOpAt 3 .NOT,
   middleTwoOpAt 4 (.Dup ⟨5, by decide⟩),
   middleTwoOpAt 5 (.Dup ⟨2, by decide⟩),
   middleTwoOpAt 6 .MUL,
   middleTwoOpAt 7 (.Swap ⟨1, by decide⟩),
   middleTwoOpAt 8 (.Dup ⟨6, by decide⟩),
   middleTwoOpAt 9 .MULMOD,
   middleTwoOpAt 10 (.Dup ⟨1, by decide⟩),
   middleTwoOpAt 11 (.Dup ⟨1, by decide⟩),
   middleTwoOpAt 12 .LT,
   middleTwoOpAt 13 .SUB,
   middleTwoOpAt 14 (.Dup ⟨4, by decide⟩),
   middleTwoOpAt 15 (.Dup ⟨2, by decide⟩),
   middleTwoOpAt 16 .ADD,
   middleTwoOpAt 17 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 18 (.Swap ⟨5, by decide⟩),
   middleTwoOpAt 19 .GT,
   middleTwoOpAt 20 .SUB,
   middleTwoOpAt 21 .SUB,
   middleTwoOpAt 22 (.Dup ⟨3, by decide⟩),
   middleTwoOpAt 23 (.Dup ⟨3, by decide⟩),
   middleTwoOpAt 24 .MLOAD,
   middleTwoOpAt 25 .ADD,
   middleTwoOpAt 26 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 27 (.Swap ⟨4, by decide⟩),
   middleTwoOpAt 28 .GT,
   middleTwoOpAt 29 .ADD,
   middleTwoOpAt 30 (.Swap ⟨2, by decide⟩),
   middleTwoOpAt 31 (.Dup ⟨2, by decide⟩),
   middleTwoPushAt 32 1 31,
   middleTwoOpAt 33 .NOT,
   middleTwoOpAt 34 .ADD,
   middleTwoOpAt 35 (.Swap ⟨2, by decide⟩),
   middleTwoOpAt 36 .MSTORE,
   middleTwoPushAt 37 1 31,
   middleTwoOpAt 38 .NOT,
   middleTwoOpAt 39 .ADD]


def secondStartIndex : Nat := 2743

private def secondTemplate : List Instr :=
  [
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 5 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 4 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 5 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.push 2 4136,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPI]

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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4263 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 2787) :
    Artifact.submissionArtifact.instructionPC index =
      [4263,4264,4265,4266,4267,4268,4269,4270,4271,4272,4273,4274,4275,4276,4277,4278,4279,4280,4281,4282,4283,4284,4285,4286,4287,4288,4289,4290,4291,4292,4293,4294,4295,4297,4298,4299,4300,4301,4303,4304,4305,4306,4307,4308,4311][index - secondStartIndex]! := by
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

/-- Final MAC and four-way loop test: instructions 2838..2879, pc 4263..4311. -/
def secondMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [secondOpAt 0 (.Dup ⟨0, by decide⟩),
   secondOpAt 1 .MLOAD,
   secondPushAt 2 0 0,
   secondOpAt 3 .NOT,
   secondOpAt 4 (.Dup ⟨5, by decide⟩),
   secondOpAt 5 (.Dup ⟨2, by decide⟩),
   secondOpAt 6 .MUL,
   secondOpAt 7 (.Swap ⟨1, by decide⟩),
   secondOpAt 8 (.Dup ⟨6, by decide⟩),
   secondOpAt 9 .MULMOD,
   secondOpAt 10 (.Dup ⟨1, by decide⟩),
   secondOpAt 11 (.Dup ⟨1, by decide⟩),
   secondOpAt 12 .LT,
   secondOpAt 13 .SUB,
   secondOpAt 14 (.Dup ⟨4, by decide⟩),
   secondOpAt 15 (.Dup ⟨2, by decide⟩),
   secondOpAt 16 .ADD,
   secondOpAt 17 (.Dup ⟨0, by decide⟩),
   secondOpAt 18 (.Swap ⟨5, by decide⟩),
   secondOpAt 19 .GT,
   secondOpAt 20 .SUB,
   secondOpAt 21 .SUB,
   secondOpAt 22 (.Dup ⟨3, by decide⟩),
   secondOpAt 23 (.Dup ⟨3, by decide⟩),
   secondOpAt 24 .MLOAD,
   secondOpAt 25 .ADD,
   secondOpAt 26 (.Dup ⟨0, by decide⟩),
   secondOpAt 27 (.Swap ⟨4, by decide⟩),
   secondOpAt 28 .GT,
   secondOpAt 29 .ADD,
   secondOpAt 30 (.Swap ⟨2, by decide⟩),
   secondOpAt 31 (.Dup ⟨2, by decide⟩),
   secondPushAt 32 1 31,
   secondOpAt 33 .NOT,
   secondOpAt 34 .ADD,
   secondOpAt 35 (.Swap ⟨2, by decide⟩),
   secondOpAt 36 .MSTORE,
   secondPushAt 37 1 31,
   secondOpAt 38 .NOT,
   secondOpAt 39 .ADD,
   secondOpAt 40 (.Dup ⟨5, by decide⟩),
   secondOpAt 41 (.Dup ⟨1, by decide⟩),
   secondOpAt 42 .GT,
   secondPushAt 43 2 4136,
   secondOpAt 44 .JUMPI]


/-- The complete four-MAC L1 block, retained for whole-block consumers. -/
def cios2L1 := firstMac ++ middleOneMac ++ middleTwoMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
