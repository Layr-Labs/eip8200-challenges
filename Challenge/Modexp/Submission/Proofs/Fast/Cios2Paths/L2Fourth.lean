import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def fourthStartIndex : Nat := 3245

private def fourthTemplate : List Instr :=
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
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop fourthStartIndex).take fourthTemplate.length = fourthTemplate := by
  rfl

private theorem fourthGetElem (offset : Nat) (hoffset : offset < fourthTemplate.length) :
    Artifact.submissionInstructions[fourthStartIndex + offset]? = fourthTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC fourthStartIndex = 5131 := by rfl

@[simp] theorem fourthPC (i : Nat) (hi : fourthStartIndex ≤ i) (hii : i ≤ 3284) :
    Artifact.submissionArtifact.instructionPC i =
      [5131, 5132, 5133, 5134, 5135, 5136, 5137, 5138, 5139, 5140, 5141, 5142, 5143, 5144, 5145, 5146, 5147, 5148, 5149, 5150, 5151, 5152, 5153, 5154, 5155, 5156, 5157, 5158, 5159, 5160, 5161, 5162, 5164, 5165, 5166, 5167, 5168, 5169, 5170, 5171][i - fourthStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (fourthStartIndex + (i - fourthStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC fourthStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop fourthStartIndex).take
              (i - fourthStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact fourthStartIndex (i - fourthStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

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
  ⟨fourthStartIndex + offset, .push width value, (fourthGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3245..3284, PCs 5131..5171. -/
def fourthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fourthOpAt 0 (.Dup ⟨0, by decide⟩),
   fourthOpAt 1 .MLOAD,
   fourthPushAt 2 0 0,
   fourthOpAt 3 .NOT,
   fourthOpAt 4 (.Dup ⟨5, by decide⟩),
   fourthOpAt 5 (.Dup ⟨2, by decide⟩),
   fourthOpAt 6 .MUL,
   fourthOpAt 7 (.Swap ⟨1, by decide⟩),
   fourthOpAt 8 (.Dup ⟨6, by decide⟩),
   fourthOpAt 9 .MULMOD,
   fourthOpAt 10 (.Dup ⟨1, by decide⟩),
   fourthOpAt 11 (.Dup ⟨1, by decide⟩),
   fourthOpAt 12 .LT,
   fourthOpAt 13 .SUB,
   fourthOpAt 14 (.Dup ⟨4, by decide⟩),
   fourthOpAt 15 (.Dup ⟨2, by decide⟩),
   fourthOpAt 16 .ADD,
   fourthOpAt 17 (.Dup ⟨0, by decide⟩),
   fourthOpAt 18 (.Swap ⟨5, by decide⟩),
   fourthOpAt 19 .GT,
   fourthOpAt 20 .SUB,
   fourthOpAt 21 .SUB,
   fourthOpAt 22 (.Dup ⟨3, by decide⟩),
   fourthOpAt 23 (.Dup ⟨3, by decide⟩),
   fourthOpAt 24 .MLOAD,
   fourthOpAt 25 .ADD,
   fourthOpAt 26 (.Dup ⟨0, by decide⟩),
   fourthOpAt 27 (.Swap ⟨4, by decide⟩),
   fourthOpAt 28 .GT,
   fourthOpAt 29 .ADD,
   fourthOpAt 30 (.Swap ⟨2, by decide⟩),
   fourthPushAt 31 1 32,
   fourthOpAt 32 (.Dup ⟨3, by decide⟩),
   fourthOpAt 33 (.Dup ⟨11, by decide⟩),
   fourthOpAt 34 .ADD,
   fourthOpAt 35 (.Swap ⟨3, by decide⟩),
   fourthOpAt 36 .ADD,
   fourthOpAt 37 .MSTORE,
   fourthOpAt 38 (.Dup ⟨8, by decide⟩),
   fourthOpAt 39 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
