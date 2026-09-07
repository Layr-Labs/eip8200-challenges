import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3366

private def template : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8256,
   .op .MSTORE,
   .op .LT,
   .push 2 8192,
   .op .MLOAD,
   .op .ADD,
   .push 2 8224,
   .op .MSTORE,
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4150,
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 2642,
   .op .JUMP]

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
    Artifact.submissionArtifact.instructionPC startIndex = 5255 := by rfl

@[simp] theorem tailPC (i : Nat) (hi : startIndex ≤ i) (hii : i ≤ 3397) :
    Artifact.submissionArtifact.instructionPC i =
      [5255, 5256, 5257, 5258, 5259, 5260, 5261, 5262, 5265, 5266, 5267, 5268, 5271, 5272, 5273, 5276, 5277, 5278, 5281, 5282, 5283, 5284, 5285, 5286, 5287, 5290, 5291, 5292, 5293, 5294, 5295, 5298][i - startIndex]! := by
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

/-- Exact live instruction slice 3366..3397, PCs 5255..5298. -/
def cios2Tail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .POP,
   opAt 1 .POP,
   opAt 2 (.Swap ⟨1, by decide⟩),
   opAt 3 .POP,
   opAt 4 .POP,
   opAt 5 .JUMPDEST,
   opAt 6 (.Dup ⟨0, by decide⟩),
   pushAt 7 2 8224,
   opAt 8 .MLOAD,
   opAt 9 .ADD,
   opAt 10 (.Dup ⟨0, by decide⟩),
   pushAt 11 2 8256,
   opAt 12 .MSTORE,
   opAt 13 .LT,
   pushAt 14 2 8192,
   opAt 15 .MLOAD,
   opAt 16 .ADD,
   pushAt 17 2 8224,
   opAt 18 .MSTORE,
   opAt 19 (.Dup ⟨3, by decide⟩),
   opAt 20 .ADD,
   opAt 21 (.Dup ⟨2, by decide⟩),
   opAt 22 (.Dup ⟨1, by decide⟩),
   opAt 23 .GT,
   pushAt 24 2 4150,
   opAt 25 .JUMPI,
   opAt 26 .POP,
   opAt 27 .POP,
   opAt 28 .POP,
   opAt 29 .POP,
   pushAt 30 2 2642,
   opAt 31 .JUMP]

def cios2TailLoop := cios2Tail.take 26

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail
