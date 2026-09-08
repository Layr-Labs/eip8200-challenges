import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2930

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [.op .JUMPDEST,
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
    Artifact.submissionArtifact.instructionPC startIndex = 4199 := by
  rfl

@[simp] theorem entryPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 2956) :
    Artifact.submissionArtifact.instructionPC index =
      [4199,4200,4203,4204,4205,4207,4208,4209,4212,4213,4214,4215,4216,4218,4219,4220,4222,4223,4224,4225,4226,4227,4228,4230,4231,4232,4233][index - startIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (startIndex + (index - startIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC startIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop startIndex).take
              (index - startIndex))).length :=
      instructionPC_add Artifact.submissionArtifact startIndex
        (index - startIndex)
    _ = _ := by
      rw [startPC]
      interval_cases index <;> rfl

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

/-- Instructions 2684..2710, pc 4225..4259. -/
def cios2Entry :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   pushAt 1 2 9344,
   opAt 2 .MLOAD,
   opAt 3 (.Dup ⟨0, by decide⟩),
   pushAt 4 1 64,
   opAt 5 .ADD,
   opAt 6 .CALLDATASIZE,
   pushAt 7 2 8192,
   opAt 8 .CALLDATACOPY,
   opAt 9 (.Dup ⟨0, by decide⟩),
   opAt 10 (.Dup ⟨3, by decide⟩),
   opAt 11 .ADD,
   pushAt 12 1 32,
   opAt 13 (.Swap ⟨0, by decide⟩),
   opAt 14 .SUB,
   pushAt 15 1 32,
   opAt 16 (.Dup ⟨4, by decide⟩),
   opAt 17 .SUB,
   opAt 18 (.Swap ⟨3, by decide⟩),
   opAt 19 .POP,
   opAt 20 (.Swap ⟨0, by decide⟩),
   opAt 21 .POP,
   pushAt 22 1 32,
   opAt 23 (.Dup ⟨2, by decide⟩),
   opAt 24 .SUB,
   opAt 25 (.Swap ⟨1, by decide⟩),
   opAt 26 .POP]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry
