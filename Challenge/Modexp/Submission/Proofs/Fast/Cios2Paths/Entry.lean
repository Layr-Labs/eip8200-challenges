import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Entry

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2580

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.push 2 9344,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.push 1 64,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.CALLDATASIZE,
 YulEvmCompiler.Instr.push 2 8192,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.CALLDATACOPY,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.POP,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.POP,
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.POP]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4080 := by
  rfl

@[simp] theorem entryPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 2606) :
    Artifact.submissionArtifact.instructionPC index =
      [4080,4081,4084,4085,4086,4088,4089,4090,4093,4094,4095,4096,4097,4099,4100,4101,4103,4104,4105,4106,4107,4108,4109,4111,4112,4113,4114][index - startIndex]! := by
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

/-- Instructions 2684..2710, pc 4080..4114. -/
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
