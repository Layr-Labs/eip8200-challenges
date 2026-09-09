import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3196

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [.op .JUMPDEST,
   .push 2 9344,
   .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩),
   .push 1 128,
   .op .EQ,
   .op (.Swap ⟨0, by decide⟩),
   .push 2 256,
   .op .EQ,
   .op .OR,
   .push 2 4481,
   .op .JUMPI,
   .push 2 1939,
   .op .JUMP]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop startIndex).take template.length = template := by
  rfl

private theorem getElem_slice (offset : Nat) (hoffset : offset < template.length) :
    Artifact.submissionInstructions[startIndex + offset]? = template[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) slice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem startPC : Artifact.submissionArtifact.instructionPC startIndex = 4458 := by
  rfl

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

/-- Exact program-counter table for the bounded dispatcher slice. -/
@[simp] theorem dispatchPC (i : Nat) (hi : startIndex ≤ i)
    (hii : i ≤ 3209) :
    Artifact.submissionArtifact.instructionPC i =
      [4458,4459,4462,4463,4464,4466,4467,4468,4471,4472,4473,4476,4477,4480][i - startIndex]! := by
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

/-- The common dispatcher prefix through `JUMPI` (indices 2670..2681). -/
def cios2DispatchGuard :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   pushAt 1 2 9344,
   opAt 2 .MLOAD,
   opAt 3 (.Dup ⟨0, by decide⟩),
   pushAt 4 1 128,
   opAt 5 .EQ,
   opAt 6 (.Swap ⟨0, by decide⟩),
   pushAt 7 2 256,
   opAt 8 .EQ,
   opAt 9 .OR,
   pushAt 10 2 4481,
   opAt 11 .JUMPI]

/-- Full fallback path (indices 2670..2683, pc 4458..4480). -/
def cios2Dispatch :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  cios2DispatchGuard ++
  [
   pushAt 12 2 1939,
   opAt 13 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Dispatch
