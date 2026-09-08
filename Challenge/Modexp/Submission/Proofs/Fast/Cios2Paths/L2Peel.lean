import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3164

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
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
    Artifact.submissionArtifact.instructionPC startIndex = 5199 := by
  rfl

@[simp] theorem peelPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 3206) :
    Artifact.submissionArtifact.instructionPC index =
      [5199,5200,5201,5202,5203,5204,5205,5206,5207,5208,5209,5210,5211,5212,5213,5214,5215,5216,5217,5218,5219,5220,5221,5222,5223,5224,5225,5226,5227,5228,5229,5230,5231,5233,5234,5236,5237,5238,5239,5240,5241,5243,5244][index - startIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (startIndex + (index - startIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC startIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop startIndex).take
              (index - startIndex))).length :=
      instructionPC_add Artifact.submissionArtifact startIndex
        (index - startIndex)
    _ = _ := by
      rw [startPC]
      interval_cases index <;> rfl


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

/-- Instructions 2930..2969, pc 5233..5278. -/
def cios2L2Peel :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   opAt 1 (.Dup ⟨0, by decide⟩),
   opAt 2 .MLOAD,
   pushAt 3 0 0,
   opAt 4 .NOT,
   opAt 5 (.Dup ⟨5, by decide⟩),
   opAt 6 (.Dup ⟨2, by decide⟩),
   opAt 7 .MUL,
   opAt 8 (.Swap ⟨1, by decide⟩),
   opAt 9 (.Dup ⟨6, by decide⟩),
   opAt 10 .MULMOD,
   opAt 11 (.Dup ⟨1, by decide⟩),
   opAt 12 (.Dup ⟨1, by decide⟩),
   opAt 13 .LT,
   opAt 14 .SUB,
   opAt 15 (.Dup ⟨4, by decide⟩),
   opAt 16 (.Dup ⟨2, by decide⟩),
   opAt 17 .ADD,
   opAt 18 (.Dup ⟨0, by decide⟩),
   opAt 19 (.Swap ⟨5, by decide⟩),
   opAt 20 .GT,
   opAt 21 .SUB,
   opAt 22 .SUB,
   opAt 23 (.Dup ⟨3, by decide⟩),
   opAt 24 (.Dup ⟨3, by decide⟩),
   opAt 25 .MLOAD,
   opAt 26 .ADD,
   opAt 27 (.Dup ⟨0, by decide⟩),
   opAt 28 (.Swap ⟨4, by decide⟩),
   opAt 29 .GT,
   opAt 30 .ADD,
   opAt 31 (.Swap ⟨2, by decide⟩),
   pushAt 32 1 32,
   opAt 33 (.Dup ⟨3, by decide⟩),
   pushAt 34 1 31,
   opAt 35 .NOT,
   opAt 36 .ADD,
   opAt 37 (.Swap ⟨3, by decide⟩),
   opAt 38 .ADD,
   opAt 39 .MSTORE,
   pushAt 40 1 31,
   opAt 41 .NOT,
   opAt 42 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel
