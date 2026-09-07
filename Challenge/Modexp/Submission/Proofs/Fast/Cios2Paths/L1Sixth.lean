import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def sixthStartIndex : Nat := 2920

private def sixthTemplate : List Instr :=
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
    Artifact.submissionArtifact.instructionPC sixthStartIndex = 4524 := by rfl

@[simp] theorem sixthPC (i : Nat) (hi : sixthStartIndex ≤ i) (hii : i ≤ 2956) :
    Artifact.submissionArtifact.instructionPC i =
      [4524, 4525, 4526, 4559, 4560, 4561, 4562, 4563, 4564, 4565, 4566, 4567, 4568, 4569, 4570, 4571, 4572, 4573, 4574, 4575, 4576, 4577, 4578, 4579, 4580, 4581, 4582, 4583, 4584, 4585, 4586, 4587, 4588, 4589, 4590, 4591, 4592][i - sixthStartIndex]! := by
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

/-- Exact live instruction slice 2920..2956, PCs 4524..4592. -/
def sixthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [sixthOpAt 0 (.Dup ⟨0, by decide⟩),
   sixthOpAt 1 .MLOAD,
   sixthPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   sixthOpAt 3 (.Dup ⟨5, by decide⟩),
   sixthOpAt 4 (.Dup ⟨2, by decide⟩),
   sixthOpAt 5 .MUL,
   sixthOpAt 6 (.Swap ⟨1, by decide⟩),
   sixthOpAt 7 (.Dup ⟨6, by decide⟩),
   sixthOpAt 8 .MULMOD,
   sixthOpAt 9 (.Dup ⟨1, by decide⟩),
   sixthOpAt 10 (.Dup ⟨1, by decide⟩),
   sixthOpAt 11 .LT,
   sixthOpAt 12 .SUB,
   sixthOpAt 13 (.Dup ⟨4, by decide⟩),
   sixthOpAt 14 (.Dup ⟨2, by decide⟩),
   sixthOpAt 15 .ADD,
   sixthOpAt 16 (.Dup ⟨0, by decide⟩),
   sixthOpAt 17 (.Swap ⟨5, by decide⟩),
   sixthOpAt 18 .GT,
   sixthOpAt 19 .SUB,
   sixthOpAt 20 .SUB,
   sixthOpAt 21 (.Dup ⟨3, by decide⟩),
   sixthOpAt 22 (.Dup ⟨3, by decide⟩),
   sixthOpAt 23 .MLOAD,
   sixthOpAt 24 .ADD,
   sixthOpAt 25 (.Dup ⟨0, by decide⟩),
   sixthOpAt 26 (.Swap ⟨4, by decide⟩),
   sixthOpAt 27 .GT,
   sixthOpAt 28 .ADD,
   sixthOpAt 29 (.Swap ⟨2, by decide⟩),
   sixthOpAt 30 (.Dup ⟨2, by decide⟩),
   sixthOpAt 31 (.Dup ⟨9, by decide⟩),
   sixthOpAt 32 .ADD,
   sixthOpAt 33 (.Swap ⟨2, by decide⟩),
   sixthOpAt 34 .MSTORE,
   sixthOpAt 35 (.Dup ⟨7, by decide⟩),
   sixthOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
