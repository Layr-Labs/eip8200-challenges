import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def seventhStartIndex : Nat := 2957

private def seventhTemplate : List Instr :=
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
    (Artifact.submissionInstructions.drop seventhStartIndex).take seventhTemplate.length = seventhTemplate := by
  rfl

private theorem seventhGetElem (offset : Nat) (hoffset : offset < seventhTemplate.length) :
    Artifact.submissionInstructions[seventhStartIndex + offset]? = seventhTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC seventhStartIndex = 4593 := by rfl

@[simp] theorem seventhPC (i : Nat) (hi : seventhStartIndex ≤ i) (hii : i ≤ 2993) :
    Artifact.submissionArtifact.instructionPC i =
      [4593, 4594, 4595, 4628, 4629, 4630, 4631, 4632, 4633, 4634, 4635, 4636, 4637, 4638, 4639, 4640, 4641, 4642, 4643, 4644, 4645, 4646, 4647, 4648, 4649, 4650, 4651, 4652, 4653, 4654, 4655, 4656, 4657, 4658, 4659, 4660, 4661][i - seventhStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (seventhStartIndex + (i - seventhStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC seventhStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop seventhStartIndex).take
              (i - seventhStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact seventhStartIndex (i - seventhStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def seventhOpAt (offset : Nat) (op : Operation)
    (hget : seventhTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < seventhTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨seventhStartIndex + offset, .op op, (seventhGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def seventhPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : seventhTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < seventhTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨seventhStartIndex + offset, .push width value, (seventhGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 2957..2993, PCs 4593..4661. -/
def seventhMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [seventhOpAt 0 (.Dup ⟨0, by decide⟩),
   seventhOpAt 1 .MLOAD,
   seventhPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   seventhOpAt 3 (.Dup ⟨5, by decide⟩),
   seventhOpAt 4 (.Dup ⟨2, by decide⟩),
   seventhOpAt 5 .MUL,
   seventhOpAt 6 (.Swap ⟨1, by decide⟩),
   seventhOpAt 7 (.Dup ⟨6, by decide⟩),
   seventhOpAt 8 .MULMOD,
   seventhOpAt 9 (.Dup ⟨1, by decide⟩),
   seventhOpAt 10 (.Dup ⟨1, by decide⟩),
   seventhOpAt 11 .LT,
   seventhOpAt 12 .SUB,
   seventhOpAt 13 (.Dup ⟨4, by decide⟩),
   seventhOpAt 14 (.Dup ⟨2, by decide⟩),
   seventhOpAt 15 .ADD,
   seventhOpAt 16 (.Dup ⟨0, by decide⟩),
   seventhOpAt 17 (.Swap ⟨5, by decide⟩),
   seventhOpAt 18 .GT,
   seventhOpAt 19 .SUB,
   seventhOpAt 20 .SUB,
   seventhOpAt 21 (.Dup ⟨3, by decide⟩),
   seventhOpAt 22 (.Dup ⟨3, by decide⟩),
   seventhOpAt 23 .MLOAD,
   seventhOpAt 24 .ADD,
   seventhOpAt 25 (.Dup ⟨0, by decide⟩),
   seventhOpAt 26 (.Swap ⟨4, by decide⟩),
   seventhOpAt 27 .GT,
   seventhOpAt 28 .ADD,
   seventhOpAt 29 (.Swap ⟨2, by decide⟩),
   seventhOpAt 30 (.Dup ⟨2, by decide⟩),
   seventhOpAt 31 (.Dup ⟨9, by decide⟩),
   seventhOpAt 32 .ADD,
   seventhOpAt 33 (.Swap ⟨2, by decide⟩),
   seventhOpAt 34 .MSTORE,
   seventhOpAt 35 (.Dup ⟨7, by decide⟩),
   seventhOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
