import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Mid

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2788

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [
 YulEvmCompiler.Instr.op EvmSemantics.Operation.POP,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.POP,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.push 2 8224,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.push 2 8224,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.push 2 8192,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.push 2 9440,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 2 9376,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.push 2 9408,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.push 2 9440,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.push 2 9408,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4312 := by
  rfl

@[simp] theorem midPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 2838) :
    Artifact.submissionArtifact.instructionPC index =
      [4312,4313,4314,4315,4318,4319,4320,4321,4324,4325,4326,4329,4330,4333,4334,4335,4338,4339,4340,4341,4344,4345,4346,4347,4348,4349,4350,4351,4352,4353,4354,4355,4356,4357,4358,4359,4360,4361,4362,4363,4364,4365,4368,4369,4371,4372,4373,4376,4377,4379,4380][index - startIndex]! := by
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

/-- Instructions 2880..2929, pc 4312..4380. -/
def cios2Mid :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .POP,
   opAt 1 .POP,
   opAt 2 (.Dup ⟨0, by decide⟩),
   pushAt 3 2 8224,
   opAt 4 .MLOAD,
   opAt 5 .ADD,
   opAt 6 (.Dup ⟨0, by decide⟩),
   pushAt 7 2 8224,
   opAt 8 .MSTORE,
   opAt 9 .LT,
   pushAt 10 2 8192,
   opAt 11 .MSTORE,
   pushAt 12 2 9440,
   opAt 13 .MLOAD,
   opAt 14 .MLOAD,
   pushAt 15 2 9376,
   opAt 16 .MLOAD,
   opAt 17 .MUL,
   opAt 18 (.Dup ⟨0, by decide⟩),
   pushAt 19 2 9408,
   opAt 20 .MLOAD,
   opAt 21 .MLOAD,
   opAt 22 (.Dup ⟨1, by decide⟩),
   opAt 23 (.Dup ⟨1, by decide⟩),
   opAt 24 .MUL,
   opAt 25 (.Swap ⟨1, by decide⟩),
   pushAt 26 0 0,
   opAt 27 .NOT,
   opAt 28 (.Swap ⟨1, by decide⟩),
   opAt 29 .MULMOD,
   opAt 30 (.Dup ⟨1, by decide⟩),
   opAt 31 (.Dup ⟨1, by decide⟩),
   opAt 32 .LT,
   opAt 33 (.Dup ⟨2, by decide⟩),
   opAt 34 .ADD,
   opAt 35 (.Swap ⟨0, by decide⟩),
   opAt 36 .SUB,
   opAt 37 (.Swap ⟨0, by decide⟩),
   pushAt 38 0 0,
   opAt 39 .LT,
   opAt 40 .ADD,
   pushAt 41 2 9440,
   opAt 42 .MLOAD,
   pushAt 43 1 32,
   opAt 44 (.Swap ⟨0, by decide⟩),
   opAt 45 .SUB,
   pushAt 46 2 9408,
   opAt 47 .MLOAD,
   pushAt 48 1 32,
   opAt 49 (.Swap ⟨0, by decide⟩),
   opAt 50 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Mid
