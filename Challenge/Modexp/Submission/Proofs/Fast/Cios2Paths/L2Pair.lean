import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

def firstStartIndex : Nat := 2882

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
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
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
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4427 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 2924) :
    Artifact.submissionArtifact.instructionPC index =
      [4427,4428,4429,4430,4431,4432,4433,4434,4435,4436,4437,4438,4439,4440,4441,4442,4443,4444,4445,4446,4447,4448,4449,4450,4451,4452,4453,4454,4455,4456,4457,4458,4459,4461,4462,4464,4465,4466,4467,4468,4469,4471,4472][index - firstStartIndex]! := by
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

/-- First paired L2 MAC: instructions 2970..3009, pc 4427..4472. -/
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
   firstPushAt 32 1 32,
   firstOpAt 33 (.Dup ⟨3, by decide⟩),
   firstPushAt 34 1 31,
   firstOpAt 35 .NOT,
   firstOpAt 36 .ADD,
   firstOpAt 37 (.Swap ⟨3, by decide⟩),
   firstOpAt 38 .ADD,
   firstOpAt 39 .MSTORE,
   firstPushAt 40 1 31,
   firstOpAt 41 .NOT,
   firstOpAt 42 .ADD]


def secondStartIndex : Nat := 2925

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
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.push 2 4427,
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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4473 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 2970) :
    Artifact.submissionArtifact.instructionPC index =
      [4473,4474,4475,4476,4477,4478,4479,4480,4481,4482,4483,4484,4485,4486,4487,4488,4489,4490,4491,4492,4493,4494,4495,4496,4497,4498,4499,4500,4501,4502,4503,4504,4506,4507,4509,4510,4511,4512,4513,4514,4515,4517,4518,4519,4520,4523][index - secondStartIndex]! := by
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

/-- Compact second L2 MAC and pair test: instructions 3010..3052, pc 4473..4523. -/
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
   secondPushAt 31 1 32,
   secondOpAt 32 (.Dup ⟨3, by decide⟩),
   secondPushAt 33 1 31,
   secondOpAt 34 .NOT,
   secondOpAt 35 .ADD,
   secondOpAt 36 (.Swap ⟨3, by decide⟩),
   secondOpAt 37 .ADD,
   secondOpAt 38 .MSTORE,
   secondOpAt 39 (.Dup ⟨0, by decide⟩),
   secondPushAt 40 1 31,
   secondOpAt 41 .NOT,
   secondOpAt 42 .ADD,
   secondOpAt 43 (.Swap ⟨0, by decide⟩),
   secondPushAt 44 2 4427,
   secondOpAt 45 .JUMPI]

/-- The body and exit share the compact block ending at JUMPI. -/
def secondMacBody := secondMac


def cios2L2Pair := firstMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
