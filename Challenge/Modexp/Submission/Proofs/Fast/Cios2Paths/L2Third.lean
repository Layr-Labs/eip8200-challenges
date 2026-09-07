import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def thirdStartIndex : Nat := 3206

private def thirdTemplate : List Instr :=
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
    (Artifact.submissionInstructions.drop thirdStartIndex).take thirdTemplate.length = thirdTemplate := by
  rfl

private theorem thirdGetElem (offset : Nat) (hoffset : offset < thirdTemplate.length) :
    Artifact.submissionInstructions[thirdStartIndex + offset]? = thirdTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC thirdStartIndex = 5059 := by rfl

@[simp] theorem thirdPC (i : Nat) (hi : thirdStartIndex ≤ i) (hii : i ≤ 3244) :
    Artifact.submissionArtifact.instructionPC i =
      [5059, 5060, 5061, 5094, 5095, 5096, 5097, 5098, 5099, 5100, 5101, 5102, 5103, 5104, 5105, 5106, 5107, 5108, 5109, 5110, 5111, 5112, 5113, 5114, 5115, 5116, 5117, 5118, 5119, 5120, 5121, 5123, 5124, 5125, 5126, 5127, 5128, 5129, 5130][i - thirdStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (thirdStartIndex + (i - thirdStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC thirdStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop thirdStartIndex).take
              (i - thirdStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact thirdStartIndex (i - thirdStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def thirdOpAt (offset : Nat) (op : Operation)
    (hget : thirdTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < thirdTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨thirdStartIndex + offset, .op op, (thirdGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def thirdPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : thirdTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < thirdTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨thirdStartIndex + offset, .push width value, (thirdGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3206..3244, PCs 5059..5130. -/
def thirdMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [thirdOpAt 0 (.Dup ⟨0, by decide⟩),
   thirdOpAt 1 .MLOAD,
   thirdPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   thirdOpAt 3 (.Dup ⟨5, by decide⟩),
   thirdOpAt 4 (.Dup ⟨2, by decide⟩),
   thirdOpAt 5 .MUL,
   thirdOpAt 6 (.Swap ⟨1, by decide⟩),
   thirdOpAt 7 (.Dup ⟨6, by decide⟩),
   thirdOpAt 8 .MULMOD,
   thirdOpAt 9 (.Dup ⟨1, by decide⟩),
   thirdOpAt 10 (.Dup ⟨1, by decide⟩),
   thirdOpAt 11 .LT,
   thirdOpAt 12 .SUB,
   thirdOpAt 13 (.Dup ⟨4, by decide⟩),
   thirdOpAt 14 (.Dup ⟨2, by decide⟩),
   thirdOpAt 15 .ADD,
   thirdOpAt 16 (.Dup ⟨0, by decide⟩),
   thirdOpAt 17 (.Swap ⟨5, by decide⟩),
   thirdOpAt 18 .GT,
   thirdOpAt 19 .SUB,
   thirdOpAt 20 .SUB,
   thirdOpAt 21 (.Dup ⟨3, by decide⟩),
   thirdOpAt 22 (.Dup ⟨3, by decide⟩),
   thirdOpAt 23 .MLOAD,
   thirdOpAt 24 .ADD,
   thirdOpAt 25 (.Dup ⟨0, by decide⟩),
   thirdOpAt 26 (.Swap ⟨4, by decide⟩),
   thirdOpAt 27 .GT,
   thirdOpAt 28 .ADD,
   thirdOpAt 29 (.Swap ⟨2, by decide⟩),
   thirdPushAt 30 1 32,
   thirdOpAt 31 (.Dup ⟨3, by decide⟩),
   thirdOpAt 32 (.Dup ⟨11, by decide⟩),
   thirdOpAt 33 .ADD,
   thirdOpAt 34 (.Swap ⟨3, by decide⟩),
   thirdOpAt 35 .ADD,
   thirdOpAt 36 .MSTORE,
   thirdOpAt 37 (.Dup ⟨8, by decide⟩),
   thirdOpAt 38 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
