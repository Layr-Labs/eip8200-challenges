import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def sixthStartIndex : Nat := 3325

private def sixthTemplate : List Instr :=
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
    (Artifact.submissionInstructions.drop sixthStartIndex).take sixthTemplate.length = sixthTemplate := by
  rfl

private theorem sixthGetElem (offset : Nat) (hoffset : offset < sixthTemplate.length) :
    Artifact.submissionInstructions[sixthStartIndex + offset]? = sixthTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC sixthStartIndex = 5213 := by rfl

@[simp] theorem sixthPC (i : Nat) (hi : sixthStartIndex ≤ i) (hii : i ≤ 3364) :
    Artifact.submissionArtifact.instructionPC i =
      [5213, 5214, 5215, 5216, 5217, 5218, 5219, 5220, 5221, 5222, 5223, 5224, 5225, 5226, 5227, 5228, 5229, 5230, 5231, 5232, 5233, 5234, 5235, 5236, 5237, 5238, 5239, 5240, 5241, 5242, 5243, 5244, 5246, 5247, 5248, 5249, 5250, 5251, 5252, 5253][i - sixthStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (sixthStartIndex + (i - sixthStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC sixthStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop sixthStartIndex).take
              (i - sixthStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact sixthStartIndex (i - sixthStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def sixthOpAt (offset : Nat) (op : Operation)
    (hget : sixthTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < sixthTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨sixthStartIndex + offset, .op op, (sixthGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def sixthPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : sixthTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < sixthTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨sixthStartIndex + offset, .push width value, (sixthGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3325..3364, PCs 5213..5253. -/
def sixthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [sixthOpAt 0 (.Dup ⟨0, by decide⟩),
   sixthOpAt 1 .MLOAD,
   sixthPushAt 2 0 0,
   sixthOpAt 3 .NOT,
   sixthOpAt 4 (.Dup ⟨5, by decide⟩),
   sixthOpAt 5 (.Dup ⟨2, by decide⟩),
   sixthOpAt 6 .MUL,
   sixthOpAt 7 (.Swap ⟨1, by decide⟩),
   sixthOpAt 8 (.Dup ⟨6, by decide⟩),
   sixthOpAt 9 .MULMOD,
   sixthOpAt 10 (.Dup ⟨1, by decide⟩),
   sixthOpAt 11 (.Dup ⟨1, by decide⟩),
   sixthOpAt 12 .LT,
   sixthOpAt 13 .SUB,
   sixthOpAt 14 (.Dup ⟨4, by decide⟩),
   sixthOpAt 15 (.Dup ⟨2, by decide⟩),
   sixthOpAt 16 .ADD,
   sixthOpAt 17 (.Dup ⟨0, by decide⟩),
   sixthOpAt 18 (.Swap ⟨5, by decide⟩),
   sixthOpAt 19 .GT,
   sixthOpAt 20 .SUB,
   sixthOpAt 21 .SUB,
   sixthOpAt 22 (.Dup ⟨3, by decide⟩),
   sixthOpAt 23 (.Dup ⟨3, by decide⟩),
   sixthOpAt 24 .MLOAD,
   sixthOpAt 25 .ADD,
   sixthOpAt 26 (.Dup ⟨0, by decide⟩),
   sixthOpAt 27 (.Swap ⟨4, by decide⟩),
   sixthOpAt 28 .GT,
   sixthOpAt 29 .ADD,
   sixthOpAt 30 (.Swap ⟨2, by decide⟩),
   sixthPushAt 31 1 32,
   sixthOpAt 32 (.Dup ⟨3, by decide⟩),
   sixthOpAt 33 (.Dup ⟨11, by decide⟩),
   sixthOpAt 34 .ADD,
   sixthOpAt 35 (.Swap ⟨3, by decide⟩),
   sixthOpAt 36 .ADD,
   sixthOpAt 37 .MSTORE,
   sixthOpAt 38 (.Dup ⟨8, by decide⟩),
   sixthOpAt 39 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
