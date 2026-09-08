import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3319

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Swap ⟨1, by decide⟩),
   .op .POP,
   .op .POP,
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
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Dup ⟨2, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .GT,
   .push 2 4260,
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 2304,
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
    Artifact.submissionArtifact.instructionPC startIndex = 5331 := by
  rfl

@[simp] theorem tailPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 3348) :
    Artifact.submissionArtifact.instructionPC index =
      [5331,5332,5333,5334,5335,5336,5337,5340,5341,5342,5343,5346,5347,5348,5351,5352,5353,5356,5357,5390,5391,5392,5393,5394,5397,5398,5399,5400,5401,5404][index - startIndex]! := by
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

/-- Instructions 3319..3348, pc 5331..5404. -/
def cios2Tail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .POP,
   opAt 1 .POP,
   opAt 2 (.Swap ⟨1, by decide⟩),
   opAt 3 .POP,
   opAt 4 .POP,
   opAt 5 (.Dup ⟨0, by decide⟩),
   pushAt 6 2 8224,
   opAt 7 .MLOAD,
   opAt 8 .ADD,
   opAt 9 (.Dup ⟨0, by decide⟩),
   pushAt 10 2 8256,
   opAt 11 .MSTORE,
   opAt 12 .LT,
   pushAt 13 2 8192,
   opAt 14 .MLOAD,
   opAt 15 .ADD,
   pushAt 16 2 8224,
   opAt 17 .MSTORE,
   pushAt 18 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 19 .ADD,
   opAt 20 (.Dup ⟨2, by decide⟩),
   opAt 21 (.Dup ⟨1, by decide⟩),
   opAt 22 .GT,
   pushAt 23 2 4260,
   opAt 24 .JUMPI,
   opAt 25 .POP,
   opAt 26 .POP,
   opAt 27 .POP,
   pushAt 28 2 2304,
   opAt 29 .JUMP]

/-- The taken outer-loop branch stops at its `JUMPI`. -/
def cios2TailLoop := cios2Tail.take 25

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail
