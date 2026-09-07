import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def selectStartIndex : Nat := 3201

private def selectTemplate : List Instr :=
  [.push 2 8224,
   .op (.Dup ⟨2, by decide⟩),
   .op .EQ,
   .push 2 5254,
   .op .JUMPI]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop selectStartIndex).take selectTemplate.length = selectTemplate := by
  rfl

private theorem selectGetElem (offset : Nat) (hoffset : offset < selectTemplate.length) :
    Artifact.submissionInstructions[selectStartIndex + offset]? = selectTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC selectStartIndex = 5050 := by rfl

@[simp] theorem selectPC (i : Nat) (hi : selectStartIndex ≤ i) (hii : i ≤ 3205) :
    Artifact.submissionArtifact.instructionPC i =
      [5050, 5053, 5054, 5055, 5058][i - selectStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (selectStartIndex + (i - selectStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC selectStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop selectStartIndex).take
              (i - selectStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact selectStartIndex (i - selectStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def selectOpAt (offset : Nat) (op : Operation)
    (hget : selectTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < selectTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨selectStartIndex + offset, .op op, (selectGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def selectPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : selectTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < selectTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨selectStartIndex + offset, .push width value, (selectGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3201..3205, PCs 5050..5058. -/
def selectBlock :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [selectPushAt 0 2 8224,
   selectOpAt 1 (.Dup ⟨2, by decide⟩),
   selectOpAt 2 .EQ,
   selectPushAt 3 2 5254,
   selectOpAt 4 .JUMPI]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
