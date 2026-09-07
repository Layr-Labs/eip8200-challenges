import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def fifthStartIndex : Nat := 3285

private def fifthTemplate : List Instr :=
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
    (Artifact.submissionInstructions.drop fifthStartIndex).take fifthTemplate.length = fifthTemplate := by
  rfl

private theorem fifthGetElem (offset : Nat) (hoffset : offset < fifthTemplate.length) :
    Artifact.submissionInstructions[fifthStartIndex + offset]? = fifthTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC fifthStartIndex = 5172 := by rfl

@[simp] theorem fifthPC (i : Nat) (hi : fifthStartIndex ≤ i) (hii : i ≤ 3324) :
    Artifact.submissionArtifact.instructionPC i =
      [5172, 5173, 5174, 5175, 5176, 5177, 5178, 5179, 5180, 5181, 5182, 5183, 5184, 5185, 5186, 5187, 5188, 5189, 5190, 5191, 5192, 5193, 5194, 5195, 5196, 5197, 5198, 5199, 5200, 5201, 5202, 5203, 5205, 5206, 5207, 5208, 5209, 5210, 5211, 5212][i - fifthStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (fifthStartIndex + (i - fifthStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC fifthStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop fifthStartIndex).take
              (i - fifthStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact fifthStartIndex (i - fifthStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def fifthOpAt (offset : Nat) (op : Operation)
    (hget : fifthTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < fifthTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨fifthStartIndex + offset, .op op, (fifthGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def fifthPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : fifthTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < fifthTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨fifthStartIndex + offset, .push width value, (fifthGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3285..3324, PCs 5172..5212. -/
def fifthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fifthOpAt 0 (.Dup ⟨0, by decide⟩),
   fifthOpAt 1 .MLOAD,
   fifthPushAt 2 0 0,
   fifthOpAt 3 .NOT,
   fifthOpAt 4 (.Dup ⟨5, by decide⟩),
   fifthOpAt 5 (.Dup ⟨2, by decide⟩),
   fifthOpAt 6 .MUL,
   fifthOpAt 7 (.Swap ⟨1, by decide⟩),
   fifthOpAt 8 (.Dup ⟨6, by decide⟩),
   fifthOpAt 9 .MULMOD,
   fifthOpAt 10 (.Dup ⟨1, by decide⟩),
   fifthOpAt 11 (.Dup ⟨1, by decide⟩),
   fifthOpAt 12 .LT,
   fifthOpAt 13 .SUB,
   fifthOpAt 14 (.Dup ⟨4, by decide⟩),
   fifthOpAt 15 (.Dup ⟨2, by decide⟩),
   fifthOpAt 16 .ADD,
   fifthOpAt 17 (.Dup ⟨0, by decide⟩),
   fifthOpAt 18 (.Swap ⟨5, by decide⟩),
   fifthOpAt 19 .GT,
   fifthOpAt 20 .SUB,
   fifthOpAt 21 .SUB,
   fifthOpAt 22 (.Dup ⟨3, by decide⟩),
   fifthOpAt 23 (.Dup ⟨3, by decide⟩),
   fifthOpAt 24 .MLOAD,
   fifthOpAt 25 .ADD,
   fifthOpAt 26 (.Dup ⟨0, by decide⟩),
   fifthOpAt 27 (.Swap ⟨4, by decide⟩),
   fifthOpAt 28 .GT,
   fifthOpAt 29 .ADD,
   fifthOpAt 30 (.Swap ⟨2, by decide⟩),
   fifthPushAt 31 1 32,
   fifthOpAt 32 (.Dup ⟨3, by decide⟩),
   fifthOpAt 33 (.Dup ⟨11, by decide⟩),
   fifthOpAt 34 .ADD,
   fifthOpAt 35 (.Swap ⟨3, by decide⟩),
   fifthOpAt 36 .ADD,
   fifthOpAt 37 .MSTORE,
   fifthOpAt 38 (.Dup ⟨8, by decide⟩),
   fifthOpAt 39 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
