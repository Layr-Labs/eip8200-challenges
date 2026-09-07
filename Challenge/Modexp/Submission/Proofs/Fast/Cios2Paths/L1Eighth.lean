import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def eighthStartIndex : Nat := 2994

private def eighthTemplate : List Instr :=
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
    (Artifact.submissionInstructions.drop eighthStartIndex).take eighthTemplate.length = eighthTemplate := by
  rfl

private theorem eighthGetElem (offset : Nat) (hoffset : offset < eighthTemplate.length) :
    Artifact.submissionInstructions[eighthStartIndex + offset]? = eighthTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC eighthStartIndex = 4662 := by rfl

@[simp] theorem eighthPC (i : Nat) (hi : eighthStartIndex ≤ i) (hii : i ≤ 3030) :
    Artifact.submissionArtifact.instructionPC i =
      [4662, 4663, 4664, 4697, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707, 4708, 4709, 4710, 4711, 4712, 4713, 4714, 4715, 4716, 4717, 4718, 4719, 4720, 4721, 4722, 4723, 4724, 4725, 4726, 4727, 4728, 4729, 4730][i - eighthStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (eighthStartIndex + (i - eighthStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC eighthStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop eighthStartIndex).take
              (i - eighthStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact eighthStartIndex (i - eighthStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def eighthOpAt (offset : Nat) (op : Operation)
    (hget : eighthTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < eighthTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨eighthStartIndex + offset, .op op, (eighthGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def eighthPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : eighthTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < eighthTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨eighthStartIndex + offset, .push width value, (eighthGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 2994..3030, PCs 4662..4730. -/
def eighthMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [eighthOpAt 0 (.Dup ⟨0, by decide⟩),
   eighthOpAt 1 .MLOAD,
   eighthPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   eighthOpAt 3 (.Dup ⟨5, by decide⟩),
   eighthOpAt 4 (.Dup ⟨2, by decide⟩),
   eighthOpAt 5 .MUL,
   eighthOpAt 6 (.Swap ⟨1, by decide⟩),
   eighthOpAt 7 (.Dup ⟨6, by decide⟩),
   eighthOpAt 8 .MULMOD,
   eighthOpAt 9 (.Dup ⟨1, by decide⟩),
   eighthOpAt 10 (.Dup ⟨1, by decide⟩),
   eighthOpAt 11 .LT,
   eighthOpAt 12 .SUB,
   eighthOpAt 13 (.Dup ⟨4, by decide⟩),
   eighthOpAt 14 (.Dup ⟨2, by decide⟩),
   eighthOpAt 15 .ADD,
   eighthOpAt 16 (.Dup ⟨0, by decide⟩),
   eighthOpAt 17 (.Swap ⟨5, by decide⟩),
   eighthOpAt 18 .GT,
   eighthOpAt 19 .SUB,
   eighthOpAt 20 .SUB,
   eighthOpAt 21 (.Dup ⟨3, by decide⟩),
   eighthOpAt 22 (.Dup ⟨3, by decide⟩),
   eighthOpAt 23 .MLOAD,
   eighthOpAt 24 .ADD,
   eighthOpAt 25 (.Dup ⟨0, by decide⟩),
   eighthOpAt 26 (.Swap ⟨4, by decide⟩),
   eighthOpAt 27 .GT,
   eighthOpAt 28 .ADD,
   eighthOpAt 29 (.Swap ⟨2, by decide⟩),
   eighthOpAt 30 (.Dup ⟨2, by decide⟩),
   eighthOpAt 31 (.Dup ⟨9, by decide⟩),
   eighthOpAt 32 .ADD,
   eighthOpAt 33 (.Swap ⟨2, by decide⟩),
   eighthOpAt 34 .MSTORE,
   eighthOpAt 35 (.Dup ⟨7, by decide⟩),
   eighthOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
