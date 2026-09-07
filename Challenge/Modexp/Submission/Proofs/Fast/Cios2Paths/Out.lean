import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Out

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2714

private def template : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 0 0,
   .push 4 9440,
   .op .MLOAD,
   .op (.Dup ⟨4, by decide⟩),
   .push 2 9344,
   .op .MLOAD,
   .op .ADD,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op .JUMPDEST,
   .op .JUMPDEST]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop startIndex).take template.length = template := by
  rfl

private theorem getElem_slice (offset : Nat) (hoffset : offset < template.length) :
    Artifact.submissionInstructions[startIndex + offset]? = template[offset]? := by
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
    Artifact.submissionArtifact.instructionPC startIndex = 4150 := by rfl

@[simp] theorem outPC (i : Nat) (hi : startIndex ≤ i) (hii : i ≤ 2728) :
    Artifact.submissionArtifact.instructionPC i =
      [4150, 4151, 4152, 4153, 4154, 4159, 4160, 4161, 4164, 4165, 4166, 4167, 4168, 4169, 4170][i - startIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (startIndex + (i - startIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC startIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop startIndex).take
              (i - startIndex))).length :=
      instructionPC_add Artifact.submissionArtifact startIndex (i - startIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def opAt (offset : Nat) (op : Operation)
    (hget : template[offset]? = some (.op op) := by rfl)
    (hoffset : offset < template.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨startIndex + offset, .op op, (getElem_slice offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def pushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : template[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < template.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨startIndex + offset, .push width value, (getElem_slice offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 2714..2728, PCs 4150..4170. -/
def cios2Out :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   opAt 1 (.Dup ⟨0, by decide⟩),
   opAt 2 .MLOAD,
   pushAt 3 0 0,
   pushAt 4 4 9440,
   opAt 5 .MLOAD,
   opAt 6 (.Dup ⟨4, by decide⟩),
   pushAt 7 2 9344,
   opAt 8 .MLOAD,
   opAt 9 .ADD,
   opAt 10 .JUMPDEST,
   opAt 11 .JUMPDEST,
   opAt 12 .JUMPDEST,
   opAt 13 .JUMPDEST,
   opAt 14 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Out
