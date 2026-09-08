import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3313

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
   .op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8256,
   .op .MSTORE,
   .op .LT,
   .push 2 8192,
   .op .MLOAD,
   .op .ADD,
   .push 2 8224,
   .op .MSTORE,
   .push 1 31,
   .op .NOT,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4843,
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 2637,
   .op .JUMP]

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
    Artifact.submissionArtifact.instructionPC startIndex = 5376 := by
  rfl

@[simp] theorem tailPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 3344) :
    Artifact.submissionArtifact.instructionPC index =
      [5376,5377,5378,5379,5380,5381,5382,5383,5386,5387,5388,5389,5392,5393,5394,5397,5398,5399,5402,5403,5405,5406,5407,5408,5409,5410,5413,5414,5415,5416,5417,5420][index - startIndex]! := by
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

/-- Instructions 3053..3083, pc 5376..5420. -/
def cios2Tail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .POP,
   opAt 1 .POP,
   opAt 2 (.Swap ⟨1, by decide⟩),
   opAt 3 .POP,
   opAt 4 .POP,
   opAt 5 .JUMPDEST,
   opAt 6 (.Dup ⟨0, by decide⟩),
   pushAt 7 2 8224,
   opAt 8 .MLOAD,
   opAt 9 .ADD,
   opAt 10 (.Dup ⟨0, by decide⟩),
   pushAt 11 2 8256,
   opAt 12 .MSTORE,
   opAt 13 .LT,
   pushAt 14 2 8192,
   opAt 15 .MLOAD,
   opAt 16 .ADD,
   pushAt 17 2 8224,
   opAt 18 .MSTORE,
   pushAt 19 1 31,
   opAt 20 .NOT,
   opAt 21 .ADD,
   opAt 22 (.Dup ⟨2, by decide⟩),
   opAt 23 (.Dup ⟨1, by decide⟩),
   opAt 24 .GT,
   pushAt 25 2 4843,
   opAt 26 .JUMPI,
   opAt 27 .POP,
   opAt 28 .POP,
   opAt 29 .POP,
   pushAt 30 2 2637,
   opAt 31 .JUMP]

/-- The taken outer-loop branch stops at its `JUMPI`. -/
def cios2TailLoop := cios2Tail.take 27

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail
