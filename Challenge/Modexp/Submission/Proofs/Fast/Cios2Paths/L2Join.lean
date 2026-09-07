import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def joinStartIndex : Nat := 3365

private def joinTemplate : List Instr :=
  [.op .JUMPDEST]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop joinStartIndex).take joinTemplate.length = joinTemplate := by
  rfl

private theorem joinGetElem (offset : Nat) (hoffset : offset < joinTemplate.length) :
    Artifact.submissionInstructions[joinStartIndex + offset]? = joinTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC joinStartIndex = 5254 := by rfl

@[simp] theorem joinPC (i : Nat) (hi : joinStartIndex ≤ i) (hii : i ≤ 3365) :
    Artifact.submissionArtifact.instructionPC i =
      [5254][i - joinStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (joinStartIndex + (i - joinStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC joinStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop joinStartIndex).take
              (i - joinStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact joinStartIndex (i - joinStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def joinOpAt (offset : Nat) (op : Operation)
    (hget : joinTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < joinTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨joinStartIndex + offset, .op op, (joinGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def joinPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : joinTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < joinTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨joinStartIndex + offset, .push width value, (joinGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3365..3365, PCs 5254..5254. -/
def joinBlock :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [joinOpAt 0 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
