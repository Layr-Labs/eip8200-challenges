import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

def peelStartIndex : Nat := 2839

private def peelTemplate : List Instr :=
  [
 YulEvmCompiler.Instr.op EvmSemantics.Operation.JUMPDEST,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.push 0 0,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 5 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MUL,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 6 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MULMOD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 1 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.LT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 4 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 2 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 5 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.SUB,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MLOAD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 0 }),
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 4 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.GT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 2 }),
 YulEvmCompiler.Instr.push 1 32,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Dup { idx := 3 }),
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op (EvmSemantics.Operation.Swap { idx := 3 }),
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.MSTORE,
 YulEvmCompiler.Instr.push 1 31,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.NOT,
 YulEvmCompiler.Instr.op EvmSemantics.Operation.ADD]

private theorem peelSlice_eq :
    (Artifact.submissionInstructions.drop peelStartIndex).take
        peelTemplate.length = peelTemplate := by
  rfl

private theorem peelGetElem (offset : Nat)
    (hoffset : offset < peelTemplate.length) :
    Artifact.submissionInstructions[peelStartIndex + offset]? =
      peelTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) peelSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem peelStartPC :
    Artifact.submissionArtifact.instructionPC peelStartIndex = 4381 := by
  rfl

@[simp] theorem peelPC (index : Nat) (hlo : peelStartIndex ≤ index)
    (hhi : index ≤ 2881) :
    Artifact.submissionArtifact.instructionPC index =
      [4381,4382,4383,4384,4385,4386,4387,4388,4389,4390,4391,4392,4393,4394,4395,4396,4397,4398,4399,4400,4401,4402,4403,4404,4405,4406,4407,4408,4409,4410,4411,4412,4413,4415,4416,4418,4419,4420,4421,4422,4423,4425,4426][index - peelStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (peelStartIndex + (index - peelStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC peelStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop peelStartIndex).take
              (index - peelStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact peelStartIndex
        (index - peelStartIndex)
    _ = _ := by
      rw [peelStartPC]
      interval_cases index <;> rfl

def peelOpAt (offset : Nat) (op : Operation)
    (hget : peelTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < peelTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨peelStartIndex + offset, .op op, (peelGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def peelPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : peelTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < peelTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨peelStartIndex + offset, .push width value,
    (peelGetElem offset hoffset).trans hget, hwf⟩

/-- Peeled L2 MAC: instructions 2930..2969, pc 4381..4426. -/
def cios2L2Peel :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [peelOpAt 0 .JUMPDEST,
   peelOpAt 1 (.Dup ⟨0, by decide⟩),
   peelOpAt 2 .MLOAD,
   peelPushAt 3 0 0,
   peelOpAt 4 .NOT,
   peelOpAt 5 (.Dup ⟨5, by decide⟩),
   peelOpAt 6 (.Dup ⟨2, by decide⟩),
   peelOpAt 7 .MUL,
   peelOpAt 8 (.Swap ⟨1, by decide⟩),
   peelOpAt 9 (.Dup ⟨6, by decide⟩),
   peelOpAt 10 .MULMOD,
   peelOpAt 11 (.Dup ⟨1, by decide⟩),
   peelOpAt 12 (.Dup ⟨1, by decide⟩),
   peelOpAt 13 .LT,
   peelOpAt 14 .SUB,
   peelOpAt 15 (.Dup ⟨4, by decide⟩),
   peelOpAt 16 (.Dup ⟨2, by decide⟩),
   peelOpAt 17 .ADD,
   peelOpAt 18 (.Dup ⟨0, by decide⟩),
   peelOpAt 19 (.Swap ⟨5, by decide⟩),
   peelOpAt 20 .GT,
   peelOpAt 21 .SUB,
   peelOpAt 22 .SUB,
   peelOpAt 23 (.Dup ⟨3, by decide⟩),
   peelOpAt 24 (.Dup ⟨3, by decide⟩),
   peelOpAt 25 .MLOAD,
   peelOpAt 26 .ADD,
   peelOpAt 27 (.Dup ⟨0, by decide⟩),
   peelOpAt 28 (.Swap ⟨4, by decide⟩),
   peelOpAt 29 .GT,
   peelOpAt 30 .ADD,
   peelOpAt 31 (.Swap ⟨2, by decide⟩),
   peelPushAt 32 1 32,
   peelOpAt 33 (.Dup ⟨3, by decide⟩),
   peelPushAt 34 1 31,
   peelOpAt 35 .NOT,
   peelOpAt 36 .ADD,
   peelOpAt 37 (.Swap ⟨3, by decide⟩),
   peelOpAt 38 .ADD,
   peelOpAt 39 .MSTORE,
   peelPushAt 40 1 31,
   peelOpAt 41 .NOT,
   peelOpAt 42 .ADD]


end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel
