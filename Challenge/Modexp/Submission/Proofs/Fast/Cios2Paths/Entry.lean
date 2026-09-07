import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2684

private def template : List Instr :=
  [.op .JUMPDEST,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Swap ⟨0, by decide⟩),
   .push 2 9344,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 64,
   .op .ADD,
   .op .CALLDATASIZE,
   .push 2 8192,
   .op .CALLDATACOPY,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .ADD,
   .push 1 32,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .push 1 32,
   .op (.Dup ⟨4, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨3, by decide⟩),
   .op .POP,
   .op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .push 1 32,
   .op (.Dup ⟨2, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4080 := by rfl

@[simp] theorem entryPC (i : Nat) (hi : startIndex ≤ i) (hii : i ≤ 2713) :
    Artifact.submissionArtifact.instructionPC i =
      [4080, 4081, 4114, 4115, 4116, 4119, 4120, 4121, 4123, 4124, 4125, 4128, 4129, 4130, 4131, 4132, 4134, 4135, 4136, 4138, 4139, 4140, 4141, 4142, 4143, 4144, 4146, 4147, 4148, 4149][i - startIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (startIndex + (i - startIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC startIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop startIndex).take
              (i - startIndex))).length :=
      instructionPC_add Artifact.submissionArtifact startIndex (i - startIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

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

/-- Exact live instruction slice 2684..2713, PCs 4080..4149. -/
def cios2Entry :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   pushAt 1 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 2 (.Swap ⟨1, by decide⟩),
   opAt 3 (.Swap ⟨0, by decide⟩),
   pushAt 4 2 9344,
   opAt 5 .MLOAD,
   opAt 6 (.Dup ⟨0, by decide⟩),
   pushAt 7 1 64,
   opAt 8 .ADD,
   opAt 9 .CALLDATASIZE,
   pushAt 10 2 8192,
   opAt 11 .CALLDATACOPY,
   opAt 12 (.Dup ⟨0, by decide⟩),
   opAt 13 (.Dup ⟨3, by decide⟩),
   opAt 14 .ADD,
   pushAt 15 1 32,
   opAt 16 (.Swap ⟨0, by decide⟩),
   opAt 17 .SUB,
   pushAt 18 1 32,
   opAt 19 (.Dup ⟨4, by decide⟩),
   opAt 20 .SUB,
   opAt 21 (.Swap ⟨3, by decide⟩),
   opAt 22 .POP,
   opAt 23 (.Swap ⟨0, by decide⟩),
   opAt 24 .POP,
   pushAt 25 1 32,
   opAt 26 (.Dup ⟨2, by decide⟩),
   opAt 27 .SUB,
   opAt 28 (.Swap ⟨1, by decide⟩),
   opAt 29 .POP]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry
