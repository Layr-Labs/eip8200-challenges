import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def thirdStartIndex : Nat := 2804

private def thirdTemplate : List Instr :=
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
   .op (.Dup ⟨9, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op .MSTORE,
   .op (.Dup ⟨7, by decide⟩),
   .op .ADD]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop thirdStartIndex).take thirdTemplate.length = thirdTemplate := by
  rfl

private theorem thirdGetElem (offset : Nat) (hoffset : offset < thirdTemplate.length) :
    Artifact.submissionInstructions[thirdStartIndex + offset]? = thirdTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) slice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem startPC :
    Artifact.submissionArtifact.instructionPC thirdStartIndex = 4310 := by rfl

@[simp] theorem thirdPC (i : Nat) (hi : thirdStartIndex ≤ i) (hii : i ≤ 2840) :
    Artifact.submissionArtifact.instructionPC i =
      [4310, 4311, 4312, 4345, 4346, 4347, 4348, 4349, 4350, 4351, 4352, 4353, 4354, 4355, 4356, 4357, 4358, 4359, 4360, 4361, 4362, 4363, 4364, 4365, 4366, 4367, 4368, 4369, 4370, 4371, 4372, 4373, 4374, 4375, 4376, 4377, 4378][i - thirdStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (thirdStartIndex + (i - thirdStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC thirdStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop thirdStartIndex).take
              (i - thirdStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact thirdStartIndex (i - thirdStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

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
  ⟨thirdStartIndex + offset, .push width value, (thirdGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 2804..2840, PCs 4310..4378. -/
def thirdMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [thirdOpAt 0 (.Dup ⟨0, by decide⟩),
   thirdOpAt 1 .MLOAD,
   thirdPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   thirdOpAt 3 (.Dup ⟨5, by decide⟩),
   thirdOpAt 4 (.Dup ⟨2, by decide⟩),
   thirdOpAt 5 .MUL,
   thirdOpAt 6 (.Swap ⟨1, by decide⟩),
   thirdOpAt 7 (.Dup ⟨6, by decide⟩),
   thirdOpAt 8 .MULMOD,
   thirdOpAt 9 (.Dup ⟨1, by decide⟩),
   thirdOpAt 10 (.Dup ⟨1, by decide⟩),
   thirdOpAt 11 .LT,
   thirdOpAt 12 .SUB,
   thirdOpAt 13 (.Dup ⟨4, by decide⟩),
   thirdOpAt 14 (.Dup ⟨2, by decide⟩),
   thirdOpAt 15 .ADD,
   thirdOpAt 16 (.Dup ⟨0, by decide⟩),
   thirdOpAt 17 (.Swap ⟨5, by decide⟩),
   thirdOpAt 18 .GT,
   thirdOpAt 19 .SUB,
   thirdOpAt 20 .SUB,
   thirdOpAt 21 (.Dup ⟨3, by decide⟩),
   thirdOpAt 22 (.Dup ⟨3, by decide⟩),
   thirdOpAt 23 .MLOAD,
   thirdOpAt 24 .ADD,
   thirdOpAt 25 (.Dup ⟨0, by decide⟩),
   thirdOpAt 26 (.Swap ⟨4, by decide⟩),
   thirdOpAt 27 .GT,
   thirdOpAt 28 .ADD,
   thirdOpAt 29 (.Swap ⟨2, by decide⟩),
   thirdOpAt 30 (.Dup ⟨2, by decide⟩),
   thirdOpAt 31 (.Dup ⟨9, by decide⟩),
   thirdOpAt 32 .ADD,
   thirdOpAt 33 (.Swap ⟨2, by decide⟩),
   thirdOpAt 34 .MSTORE,
   thirdOpAt 35 (.Dup ⟨7, by decide⟩),
   thirdOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
