import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2997

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Swap ⟨0, by decide⟩),
   .op .POP,
   .op (.Swap ⟨0, by decide⟩),
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
   .push 2 4115,
   .op .JUMPI,
   .op .POP,
   .op .POP,
   .op .POP,
   .push 2 2642,
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
    Artifact.submissionArtifact.instructionPC startIndex = 4954 := by
  rfl

@[simp] theorem tailPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 3027) :
    Artifact.submissionArtifact.instructionPC index =
      [4954, 4955, 4956, 4957, 4958, 4959, 4960, 4961, 4964,
       4965, 4966, 4967, 4970, 4971, 4972, 4975, 4976, 4977,
       4980, 4981, 5014, 5015, 5016, 5017, 5018, 5021, 5022,
       5023, 5024, 5025, 5028][index - startIndex]! := by
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

/-- Instructions 2997..3027, pc 4954..5028. -/
def cios2Tail :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .POP,
   opAt 1 .POP,
   opAt 2 (.Swap ⟨0, by decide⟩),
   opAt 3 .POP,
   opAt 4 (.Swap ⟨0, by decide⟩),
   opAt 5 .POP,
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
   pushAt 19 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 20 .ADD,
   opAt 21 (.Dup ⟨2, by decide⟩),
   opAt 22 (.Dup ⟨1, by decide⟩),
   opAt 23 .GT,
   pushAt 24 2 4115,
   opAt 25 .JUMPI,
   opAt 26 .POP,
   opAt 27 .POP,
   opAt 28 .POP,
   pushAt 29 2 2642,
   opAt 30 .JUMP]

/-- The taken outer-loop branch stops at its `JUMPI`. -/
def cios2TailLoop := cios2Tail.take 26

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Tail
