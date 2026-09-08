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

def firstStartIndex : Nat := 3224

private def firstTemplate : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 0 0,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .push 1 32,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op .MSTORE,
   .push 1 31,
   .op .NOT,
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
    Artifact.submissionArtifact.instructionPC firstStartIndex = 5279 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 3266) :
    Artifact.submissionArtifact.instructionPC index =
      [5279,5280,5281,5282,5283,5284,5285,5286,5287,5288,5289,5290,5291,5292,5293,5294,5295,5296,5297,5298,5299,5300,5301,5302,5303,5304,5305,5306,5307,5308,5309,5310,5311,5313,5314,5316,5317,5318,5319,5320,5321,5323,5324][index - firstStartIndex]! := by
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

/-- Instructions 2970..3009, pc 5279..5324. -/
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

def secondStartIndex : Nat := 3267

private def secondTemplate : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 0 0,
   .op .NOT,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .push 1 32,
   .op (.Dup ⟨3, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op .MSTORE,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 5279,
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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 5325 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 3312) :
    Artifact.submissionArtifact.instructionPC index =
      [5325,5326,5327,5328,5329,5330,5331,5332,5333,5334,5335,5336,5337,5338,5339,5340,5341,5342,5343,5344,5345,5346,5347,5348,5349,5350,5351,5352,5353,5354,5355,5356,5358,5359,5361,5362,5363,5364,5365,5366,5367,5369,5370,5371,5372,5375][index - secondStartIndex]! := by
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

/-- Instructions 3010..3052, pc 5325..5375. -/
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
   secondPushAt 44 2 5279,
   secondOpAt 45 .JUMPI]

/-- The body and exit share the compact block ending at JUMPI. -/
def secondMacBody := secondMac.take 46

/-- The complete pair block, retained for whole-block consumers. -/
def cios2L2Pair := firstMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
