import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Out

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2607

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.push 4 9440,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.push 2 9344,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4115 := by
  rfl

@[simp] theorem outPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 2621) :
    Artifact.submissionArtifact.instructionPC index =
      [4115,4116,4117,4118,4119,4124,4125,4126,4129,4130,4131,4132,4133,4134,4135][index - startIndex]! := by
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

/-- Instructions 2711..2725, pc 4115..4135. -/
def cios2Out :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   opAt 1 (.Dup ⟨0, by decide⟩),
   opAt 2 .MLOAD,
   pushAt 3 0 0,
   pushAt 4 4 9440,
   opAt 5 .MLOAD,
   opAt 6 (.Dup ⟨4, by decide⟩),
   pushAt 7 2 9344,
   opAt 8 .MLOAD,
   opAt 9 .ADD,
   opAt 10 .JUMPDEST,
   opAt 11 .JUMPDEST,
   opAt 12 .JUMPDEST,
   opAt 13 .JUMPDEST,
   opAt 14 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Out
