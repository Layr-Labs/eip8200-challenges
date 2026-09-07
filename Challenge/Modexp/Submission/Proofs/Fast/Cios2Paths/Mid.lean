import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Mid

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3032

private def template : List Instr :=
  [.op .POP,
   .op .POP,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 8224,
   .op .MSTORE,
   .op .LT,
   .push 2 8192,
   .op .MSTORE,
   .push 2 9440,
   .op .MLOAD,
   .op .MLOAD,
   .push 2 9376,
   .op .MLOAD,
   .op .MUL,
   .op (.Dup ⟨0, by decide⟩),
   .push 2 9408,
   .op .MLOAD,
   .op .MLOAD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Swap ⟨1, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .op (.Swap ⟨0, by decide⟩),
   .push 0 0,
   .op .LT,
   .op .ADD,
   .push 2 9440,
   .op .MLOAD,
   .push 1 32,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB,
   .push 2 9408,
   .op .MLOAD,
   .push 1 32,
   .op (.Swap ⟨0, by decide⟩),
   .op .SUB]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4732 := by rfl

@[simp] theorem midPC (i : Nat) (hi : startIndex ≤ i) (hii : i ≤ 3081) :
    Artifact.submissionArtifact.instructionPC i =
      [4732, 4733, 4734, 4735, 4738, 4739, 4740, 4741, 4744, 4745, 4746, 4749, 4750, 4753, 4754, 4755, 4758, 4759, 4760, 4761, 4764, 4765, 4766, 4767, 4768, 4769, 4770, 4803, 4804, 4805, 4806, 4807, 4808, 4809, 4810, 4811, 4812, 4813, 4814, 4815, 4816, 4819, 4820, 4822, 4823, 4824, 4827, 4828, 4830, 4831][i - startIndex]! := by
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

/-- Exact live instruction slice 3032..3081, PCs 4732..4831. -/
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
   pushAt 26 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 27 (.Swap ⟨1, by decide⟩),
   opAt 28 .MULMOD,
   opAt 29 (.Dup ⟨1, by decide⟩),
   opAt 30 (.Dup ⟨1, by decide⟩),
   opAt 31 .LT,
   opAt 32 (.Dup ⟨2, by decide⟩),
   opAt 33 .ADD,
   opAt 34 (.Swap ⟨0, by decide⟩),
   opAt 35 .SUB,
   opAt 36 (.Swap ⟨0, by decide⟩),
   pushAt 37 0 0,
   opAt 38 .LT,
   opAt 39 .ADD,
   pushAt 40 2 9440,
   opAt 41 .MLOAD,
   pushAt 42 1 32,
   opAt 43 (.Swap ⟨0, by decide⟩),
   opAt 44 .SUB,
   pushAt 45 2 9408,
   opAt 46 .MLOAD,
   pushAt 47 1 32,
   opAt 48 (.Swap ⟨0, by decide⟩),
   opAt 49 .SUB]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.Mid
