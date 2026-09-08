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

def firstStartIndex : Nat := 2951

private def firstTemplate : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
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
   .op (.Dup ⟨2, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
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
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4830 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 2990) :
    Artifact.submissionArtifact.instructionPC index =
      [4830,4831,4832,4833,4866,4867,4868,4869,4870,4871,4872,4873,4874,4875,4876,4877,4878,4879,4880,4881,4882,4883,4884,4885,4886,4887,4888,4889,4890,4891,4892,4893,4894,4896,4897,4898,4899,4900,4902,4903][index - firstStartIndex]! := by
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

/-- Instructions 2726..2763, pc 4864..4937. -/
def firstMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [firstOpAt 0 .JUMPDEST,
   firstOpAt 1 (.Dup ⟨0, by decide⟩),
   firstOpAt 2 .MLOAD,
   firstPushAt 3 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   firstOpAt 4 (.Dup ⟨5, by decide⟩),
   firstOpAt 5 (.Dup ⟨2, by decide⟩),
   firstOpAt 6 .MUL,
   firstOpAt 7 (.Swap ⟨1, by decide⟩),
   firstOpAt 8 (.Dup ⟨6, by decide⟩),
   firstOpAt 9 .MULMOD,
   firstOpAt 10 (.Dup ⟨1, by decide⟩),
   firstOpAt 11 (.Dup ⟨1, by decide⟩),
   firstOpAt 12 .LT,
   firstOpAt 13 .SUB,
   firstOpAt 14 (.Dup ⟨4, by decide⟩),
   firstOpAt 15 (.Dup ⟨2, by decide⟩),
   firstOpAt 16 .ADD,
   firstOpAt 17 (.Dup ⟨0, by decide⟩),
   firstOpAt 18 (.Swap ⟨5, by decide⟩),
   firstOpAt 19 .GT,
   firstOpAt 20 .SUB,
   firstOpAt 21 .SUB,
   firstOpAt 22 (.Dup ⟨3, by decide⟩),
   firstOpAt 23 (.Dup ⟨3, by decide⟩),
   firstOpAt 24 .MLOAD,
   firstOpAt 25 .ADD,
   firstOpAt 26 (.Dup ⟨0, by decide⟩),
   firstOpAt 27 (.Swap ⟨4, by decide⟩),
   firstOpAt 28 .GT,
   firstOpAt 29 .ADD,
   firstOpAt 30 (.Swap ⟨2, by decide⟩),
   firstOpAt 31 (.Dup ⟨2, by decide⟩),
   firstPushAt 32 1 31,
   firstOpAt 33 .NOT,
   firstOpAt 34 .ADD,
   firstOpAt 35 (.Swap ⟨2, by decide⟩),
   firstOpAt 36 .MSTORE,
   firstPushAt 37 1 31,
   firstOpAt 38 .NOT,
   firstOpAt 39 .ADD]
def middleOneStartIndex : Nat := 2991

private def middleOneTemplate : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
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
   .op (.Dup ⟨2, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MSTORE,
   .push 1 31,
   .op .NOT,
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
    Artifact.submissionArtifact.instructionPC middleOneStartIndex = 4904 := by
  rfl

@[simp] theorem middleOnePC (index : Nat) (hlo : middleOneStartIndex ≤ index)
    (hhi : index ≤ 3029) :
    Artifact.submissionArtifact.instructionPC index =
      [4904,4905,4906,4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4953,4954,4955,4956,4957,4958,4959,4960,4961,4962,4963,4964,4965,4966,4967,4969,4970,4971,4972,4973,4975,4976][index - middleOneStartIndex]! := by
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

/-- Instructions 2764..2800, pc 4938..5010. -/
def middleOneMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [middleOneOpAt 0 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 1 .MLOAD,
   middleOnePushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   middleOneOpAt 3 (.Dup ⟨5, by decide⟩),
   middleOneOpAt 4 (.Dup ⟨2, by decide⟩),
   middleOneOpAt 5 .MUL,
   middleOneOpAt 6 (.Swap ⟨1, by decide⟩),
   middleOneOpAt 7 (.Dup ⟨6, by decide⟩),
   middleOneOpAt 8 .MULMOD,
   middleOneOpAt 9 (.Dup ⟨1, by decide⟩),
   middleOneOpAt 10 (.Dup ⟨1, by decide⟩),
   middleOneOpAt 11 .LT,
   middleOneOpAt 12 .SUB,
   middleOneOpAt 13 (.Dup ⟨4, by decide⟩),
   middleOneOpAt 14 (.Dup ⟨2, by decide⟩),
   middleOneOpAt 15 .ADD,
   middleOneOpAt 16 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 17 (.Swap ⟨5, by decide⟩),
   middleOneOpAt 18 .GT,
   middleOneOpAt 19 .SUB,
   middleOneOpAt 20 .SUB,
   middleOneOpAt 21 (.Dup ⟨3, by decide⟩),
   middleOneOpAt 22 (.Dup ⟨3, by decide⟩),
   middleOneOpAt 23 .MLOAD,
   middleOneOpAt 24 .ADD,
   middleOneOpAt 25 (.Dup ⟨0, by decide⟩),
   middleOneOpAt 26 (.Swap ⟨4, by decide⟩),
   middleOneOpAt 27 .GT,
   middleOneOpAt 28 .ADD,
   middleOneOpAt 29 (.Swap ⟨2, by decide⟩),
   middleOneOpAt 30 (.Dup ⟨2, by decide⟩),
   middleOnePushAt 31 1 31,
   middleOneOpAt 32 .NOT,
   middleOneOpAt 33 .ADD,
   middleOneOpAt 34 (.Swap ⟨2, by decide⟩),
   middleOneOpAt 35 .MSTORE,
   middleOnePushAt 36 1 31,
   middleOneOpAt 37 .NOT,
   middleOneOpAt 38 .ADD]
def middleTwoStartIndex : Nat := 3030

private def middleTwoTemplate : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
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
   .op (.Dup ⟨2, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MSTORE,
   .push 1 31,
   .op .NOT,
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
    Artifact.submissionArtifact.instructionPC middleTwoStartIndex = 4977 := by
  rfl

@[simp] theorem middleTwoPC (index : Nat) (hlo : middleTwoStartIndex ≤ index)
    (hhi : index ≤ 3068) :
    Artifact.submissionArtifact.instructionPC index =
      [4977,4978,4979,5012,5013,5014,5015,5016,5017,5018,5019,5020,5021,5022,5023,5024,5025,5026,5027,5028,5029,5030,5031,5032,5033,5034,5035,5036,5037,5038,5039,5040,5042,5043,5044,5045,5046,5048,5049][index - middleTwoStartIndex]! := by
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

/-- Instructions 2801..2837, pc 5011..5083. -/
def middleTwoMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [middleTwoOpAt 0 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 1 .MLOAD,
   middleTwoPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   middleTwoOpAt 3 (.Dup ⟨5, by decide⟩),
   middleTwoOpAt 4 (.Dup ⟨2, by decide⟩),
   middleTwoOpAt 5 .MUL,
   middleTwoOpAt 6 (.Swap ⟨1, by decide⟩),
   middleTwoOpAt 7 (.Dup ⟨6, by decide⟩),
   middleTwoOpAt 8 .MULMOD,
   middleTwoOpAt 9 (.Dup ⟨1, by decide⟩),
   middleTwoOpAt 10 (.Dup ⟨1, by decide⟩),
   middleTwoOpAt 11 .LT,
   middleTwoOpAt 12 .SUB,
   middleTwoOpAt 13 (.Dup ⟨4, by decide⟩),
   middleTwoOpAt 14 (.Dup ⟨2, by decide⟩),
   middleTwoOpAt 15 .ADD,
   middleTwoOpAt 16 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 17 (.Swap ⟨5, by decide⟩),
   middleTwoOpAt 18 .GT,
   middleTwoOpAt 19 .SUB,
   middleTwoOpAt 20 .SUB,
   middleTwoOpAt 21 (.Dup ⟨3, by decide⟩),
   middleTwoOpAt 22 (.Dup ⟨3, by decide⟩),
   middleTwoOpAt 23 .MLOAD,
   middleTwoOpAt 24 .ADD,
   middleTwoOpAt 25 (.Dup ⟨0, by decide⟩),
   middleTwoOpAt 26 (.Swap ⟨4, by decide⟩),
   middleTwoOpAt 27 .GT,
   middleTwoOpAt 28 .ADD,
   middleTwoOpAt 29 (.Swap ⟨2, by decide⟩),
   middleTwoOpAt 30 (.Dup ⟨2, by decide⟩),
   middleTwoPushAt 31 1 31,
   middleTwoOpAt 32 .NOT,
   middleTwoOpAt 33 .ADD,
   middleTwoOpAt 34 (.Swap ⟨2, by decide⟩),
   middleTwoOpAt 35 .MSTORE,
   middleTwoPushAt 36 1 31,
   middleTwoOpAt 37 .NOT,
   middleTwoOpAt 38 .ADD]
def secondStartIndex : Nat := 3069

private def secondTemplate : List Instr :=
  [.op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
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
   .op (.Dup ⟨2, by decide⟩),
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MSTORE,
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4830,
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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 5050 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 3112) :
    Artifact.submissionArtifact.instructionPC index =
      [5050,5051,5052,5085,5086,5087,5088,5089,5090,5091,5092,5093,5094,5095,5096,5097,5098,5099,5100,5101,5102,5103,5104,5105,5106,5107,5108,5109,5110,5111,5112,5113,5115,5116,5117,5118,5119,5121,5122,5123,5124,5125,5126,5129][index - secondStartIndex]! := by
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

/-- Instructions 2838..2879, pc 5084..5163. -/
def secondMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [secondOpAt 0 (.Dup ⟨0, by decide⟩),
   secondOpAt 1 .MLOAD,
   secondPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   secondOpAt 3 (.Dup ⟨5, by decide⟩),
   secondOpAt 4 (.Dup ⟨2, by decide⟩),
   secondOpAt 5 .MUL,
   secondOpAt 6 (.Swap ⟨1, by decide⟩),
   secondOpAt 7 (.Dup ⟨6, by decide⟩),
   secondOpAt 8 .MULMOD,
   secondOpAt 9 (.Dup ⟨1, by decide⟩),
   secondOpAt 10 (.Dup ⟨1, by decide⟩),
   secondOpAt 11 .LT,
   secondOpAt 12 .SUB,
   secondOpAt 13 (.Dup ⟨4, by decide⟩),
   secondOpAt 14 (.Dup ⟨2, by decide⟩),
   secondOpAt 15 .ADD,
   secondOpAt 16 (.Dup ⟨0, by decide⟩),
   secondOpAt 17 (.Swap ⟨5, by decide⟩),
   secondOpAt 18 .GT,
   secondOpAt 19 .SUB,
   secondOpAt 20 .SUB,
   secondOpAt 21 (.Dup ⟨3, by decide⟩),
   secondOpAt 22 (.Dup ⟨3, by decide⟩),
   secondOpAt 23 .MLOAD,
   secondOpAt 24 .ADD,
   secondOpAt 25 (.Dup ⟨0, by decide⟩),
   secondOpAt 26 (.Swap ⟨4, by decide⟩),
   secondOpAt 27 .GT,
   secondOpAt 28 .ADD,
   secondOpAt 29 (.Swap ⟨2, by decide⟩),
   secondOpAt 30 (.Dup ⟨2, by decide⟩),
   secondPushAt 31 1 31,
   secondOpAt 32 .NOT,
   secondOpAt 33 .ADD,
   secondOpAt 34 (.Swap ⟨2, by decide⟩),
   secondOpAt 35 .MSTORE,
   secondPushAt 36 1 31,
   secondOpAt 37 .NOT,
   secondOpAt 38 .ADD,
   secondOpAt 39 (.Dup ⟨5, by decide⟩),
   secondOpAt 40 (.Dup ⟨1, by decide⟩),
   secondOpAt 41 .GT,
   secondPushAt 42 2 4830,
   secondOpAt 43 .JUMPI]

/-- The body and exit share the compact block ending at JUMPI. -/
def secondMacBody := secondMac.take 44

/-- The complete four-MAC L1 block, retained for whole-block consumers. -/
def cios2L1 := firstMac ++ middleOneMac ++ middleTwoMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
