import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def secondStartIndex : Nat := 2767

private def secondTemplate : List Instr :=
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
    (Artifact.submissionInstructions.drop secondStartIndex).take secondTemplate.length = secondTemplate := by
  rfl

private theorem secondGetElem (offset : Nat) (hoffset : offset < secondTemplate.length) :
    Artifact.submissionInstructions[secondStartIndex + offset]? = secondTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4241 := by rfl

@[simp] theorem secondPC (i : Nat) (hi : secondStartIndex ≤ i) (hii : i ≤ 2803) :
    Artifact.submissionArtifact.instructionPC i =
      [4241, 4242, 4243, 4276, 4277, 4278, 4279, 4280, 4281, 4282, 4283, 4284, 4285, 4286, 4287, 4288, 4289, 4290, 4291, 4292, 4293, 4294, 4295, 4296, 4297, 4298, 4299, 4300, 4301, 4302, 4303, 4304, 4305, 4306, 4307, 4308, 4309][i - secondStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (secondStartIndex + (i - secondStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC secondStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop secondStartIndex).take
              (i - secondStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact secondStartIndex (i - secondStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def secondOpAt (offset : Nat) (op : Operation)
    (hget : secondTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < secondTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨secondStartIndex + offset, .op op, (secondGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def secondPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : secondTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < secondTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨secondStartIndex + offset, .push width value, (secondGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 2767..2803, PCs 4241..4309. -/
def secondMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [secondOpAt 0 (.Dup ⟨0, by decide⟩),
   secondOpAt 1 .MLOAD,
   secondPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   secondOpAt 3 (.Dup ⟨5, by decide⟩),
   secondOpAt 4 (.Dup ⟨2, by decide⟩),
   secondOpAt 5 .MUL,
   secondOpAt 6 (.Swap ⟨1, by decide⟩),
   secondOpAt 7 (.Dup ⟨6, by decide⟩),
   secondOpAt 8 .MULMOD,
   secondOpAt 9 (.Dup ⟨1, by decide⟩),
   secondOpAt 10 (.Dup ⟨1, by decide⟩),
   secondOpAt 11 .LT,
   secondOpAt 12 .SUB,
   secondOpAt 13 (.Dup ⟨4, by decide⟩),
   secondOpAt 14 (.Dup ⟨2, by decide⟩),
   secondOpAt 15 .ADD,
   secondOpAt 16 (.Dup ⟨0, by decide⟩),
   secondOpAt 17 (.Swap ⟨5, by decide⟩),
   secondOpAt 18 .GT,
   secondOpAt 19 .SUB,
   secondOpAt 20 .SUB,
   secondOpAt 21 (.Dup ⟨3, by decide⟩),
   secondOpAt 22 (.Dup ⟨3, by decide⟩),
   secondOpAt 23 .MLOAD,
   secondOpAt 24 .ADD,
   secondOpAt 25 (.Dup ⟨0, by decide⟩),
   secondOpAt 26 (.Swap ⟨4, by decide⟩),
   secondOpAt 27 .GT,
   secondOpAt 28 .ADD,
   secondOpAt 29 (.Swap ⟨2, by decide⟩),
   secondOpAt 30 (.Dup ⟨2, by decide⟩),
   secondOpAt 31 (.Dup ⟨9, by decide⟩),
   secondOpAt 32 .ADD,
   secondOpAt 33 (.Swap ⟨2, by decide⟩),
   secondOpAt 34 .MSTORE,
   secondOpAt 35 (.Dup ⟨7, by decide⟩),
   secondOpAt 36 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
