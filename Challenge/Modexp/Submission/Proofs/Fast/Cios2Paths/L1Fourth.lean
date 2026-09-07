import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def fourthStartIndex : Nat := 2841

private def fourthTemplate : List Instr :=
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
    Artifact.submissionArtifact.instructionPC fourthStartIndex = 4379 := by rfl

@[simp] theorem fourthPC (i : Nat) (hi : fourthStartIndex ≤ i) (hii : i ≤ 2877) :
    Artifact.submissionArtifact.instructionPC i =
      [4379, 4380, 4381, 4414, 4415, 4416, 4417, 4418, 4419, 4420, 4421, 4422, 4423, 4424, 4425, 4426, 4427, 4428, 4429, 4430, 4431, 4432, 4433, 4434, 4435, 4436, 4437, 4438, 4439, 4440, 4441, 4442, 4443, 4444, 4445, 4446, 4447][i - fourthStartIndex]! := by
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

/-- Exact live instruction slice 2841..2877, PCs 4379..4447. -/
def fourthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fourthOpAt 0 (.Dup ⟨0, by decide⟩),
   fourthOpAt 1 .MLOAD,
   fourthPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   fourthOpAt 3 (.Dup ⟨5, by decide⟩),
   fourthOpAt 4 (.Dup ⟨2, by decide⟩),
   fourthOpAt 5 .MUL,
   fourthOpAt 6 (.Swap ⟨1, by decide⟩),
   fourthOpAt 7 (.Dup ⟨6, by decide⟩),
   fourthOpAt 8 .MULMOD,
   fourthOpAt 9 (.Dup ⟨1, by decide⟩),
   fourthOpAt 10 (.Dup ⟨1, by decide⟩),
   fourthOpAt 11 .LT,
   fourthOpAt 12 .SUB,
   fourthOpAt 13 (.Dup ⟨4, by decide⟩),
   fourthOpAt 14 (.Dup ⟨2, by decide⟩),
   fourthOpAt 15 .ADD,
   fourthOpAt 16 (.Dup ⟨0, by decide⟩),
   fourthOpAt 17 (.Swap ⟨5, by decide⟩),
   fourthOpAt 18 .GT,
   fourthOpAt 19 .SUB,
   fourthOpAt 20 .SUB,
   fourthOpAt 21 (.Dup ⟨3, by decide⟩),
   fourthOpAt 22 (.Dup ⟨3, by decide⟩),
   fourthOpAt 23 .MLOAD,
   fourthOpAt 24 .ADD,
   fourthOpAt 25 (.Dup ⟨0, by decide⟩),
   fourthOpAt 26 (.Swap ⟨4, by decide⟩),
   fourthOpAt 27 .GT,
   fourthOpAt 28 .ADD,
   fourthOpAt 29 (.Swap ⟨2, by decide⟩),
   fourthOpAt 30 (.Dup ⟨2, by decide⟩),
   fourthOpAt 31 (.Dup ⟨9, by decide⟩),
   fourthOpAt 32 .ADD,
   fourthOpAt 33 (.Swap ⟨2, by decide⟩),
   fourthOpAt 34 .MSTORE,
   fourthOpAt 35 (.Dup ⟨7, by decide⟩),
   fourthOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
