import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def fifthStartIndex : Nat := 2883

private def fifthTemplate : List Instr :=
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
    Artifact.submissionArtifact.instructionPC fifthStartIndex = 4455 := by rfl

@[simp] theorem fifthPC (i : Nat) (hi : fifthStartIndex ≤ i) (hii : i ≤ 2919) :
    Artifact.submissionArtifact.instructionPC i =
      [4455, 4456, 4457, 4490, 4491, 4492, 4493, 4494, 4495, 4496, 4497, 4498, 4499, 4500, 4501, 4502, 4503, 4504, 4505, 4506, 4507, 4508, 4509, 4510, 4511, 4512, 4513, 4514, 4515, 4516, 4517, 4518, 4519, 4520, 4521, 4522, 4523][i - fifthStartIndex]! := by
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

/-- Exact live instruction slice 2883..2919, PCs 4455..4523. -/
def fifthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [fifthOpAt 0 (.Dup ⟨0, by decide⟩),
   fifthOpAt 1 .MLOAD,
   fifthPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   fifthOpAt 3 (.Dup ⟨5, by decide⟩),
   fifthOpAt 4 (.Dup ⟨2, by decide⟩),
   fifthOpAt 5 .MUL,
   fifthOpAt 6 (.Swap ⟨1, by decide⟩),
   fifthOpAt 7 (.Dup ⟨6, by decide⟩),
   fifthOpAt 8 .MULMOD,
   fifthOpAt 9 (.Dup ⟨1, by decide⟩),
   fifthOpAt 10 (.Dup ⟨1, by decide⟩),
   fifthOpAt 11 .LT,
   fifthOpAt 12 .SUB,
   fifthOpAt 13 (.Dup ⟨4, by decide⟩),
   fifthOpAt 14 (.Dup ⟨2, by decide⟩),
   fifthOpAt 15 .ADD,
   fifthOpAt 16 (.Dup ⟨0, by decide⟩),
   fifthOpAt 17 (.Swap ⟨5, by decide⟩),
   fifthOpAt 18 .GT,
   fifthOpAt 19 .SUB,
   fifthOpAt 20 .SUB,
   fifthOpAt 21 (.Dup ⟨3, by decide⟩),
   fifthOpAt 22 (.Dup ⟨3, by decide⟩),
   fifthOpAt 23 .MLOAD,
   fifthOpAt 24 .ADD,
   fifthOpAt 25 (.Dup ⟨0, by decide⟩),
   fifthOpAt 26 (.Swap ⟨4, by decide⟩),
   fifthOpAt 27 .GT,
   fifthOpAt 28 .ADD,
   fifthOpAt 29 (.Swap ⟨2, by decide⟩),
   fifthOpAt 30 (.Dup ⟨2, by decide⟩),
   fifthOpAt 31 (.Dup ⟨9, by decide⟩),
   fifthOpAt 32 .ADD,
   fifthOpAt 33 (.Swap ⟨2, by decide⟩),
   fifthOpAt 34 .MSTORE,
   fifthOpAt 35 (.Dup ⟨7, by decide⟩),
   fifthOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
