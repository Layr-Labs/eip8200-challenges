import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 3171

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [   .op (.Dup ⟨0, by decide⟩),
   .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .MUL,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
   .op .LT,
   .op .SUB,
   .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨5, by decide⟩),
   .op .GT,
   .op .SUB,
   .op .SUB,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op .ADD,
   .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨4, by decide⟩),
   .op .GT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .push 1 32,
   .op (.Dup ⟨3, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4890 := by
  rfl

@[simp] theorem peelPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 3209) :
    Artifact.submissionArtifact.instructionPC index =
      [4890,4891,4892,4925,4926,4927,4928,4929,4930,4931,4932,4933,4934,4935,4936,4937,4938,4939,4940,4941,4942,4943,4944,4945,4946,4947,4948,4949,4950,4951,4952,4954,4955,4988,4989,4990,4991,4992,5025][index - startIndex]! := by
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

/-- Instructions 2930..2969, pc 4921..5057. -/
def cios2L2Peel :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [   opAt 0 (.Dup ⟨0, by decide⟩),
   opAt 1 .MLOAD,
   pushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 3 (.Dup ⟨5, by decide⟩),
   opAt 4 (.Dup ⟨2, by decide⟩),
   opAt 5 .MUL,
   opAt 6 (.Swap ⟨1, by decide⟩),
   opAt 7 (.Dup ⟨6, by decide⟩),
   opAt 8 .MULMOD,
   opAt 9 (.Dup ⟨1, by decide⟩),
   opAt 10 (.Dup ⟨1, by decide⟩),
   opAt 11 .LT,
   opAt 12 .SUB,
   opAt 13 (.Dup ⟨4, by decide⟩),
   opAt 14 (.Dup ⟨2, by decide⟩),
   opAt 15 .ADD,
   opAt 16 (.Dup ⟨0, by decide⟩),
   opAt 17 (.Swap ⟨5, by decide⟩),
   opAt 18 .GT,
   opAt 19 .SUB,
   opAt 20 .SUB,
   opAt 21 (.Dup ⟨3, by decide⟩),
   opAt 22 (.Dup ⟨3, by decide⟩),
   opAt 23 .MLOAD,
   opAt 24 .ADD,
   opAt 25 (.Dup ⟨0, by decide⟩),
   opAt 26 (.Swap ⟨4, by decide⟩),
   opAt 27 .GT,
   opAt 28 .ADD,
   opAt 29 (.Swap ⟨2, by decide⟩),
   pushAt 30 1 32,
   opAt 31 (.Dup ⟨3, by decide⟩),
   pushAt 32 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 33 .ADD,
   opAt 34 (.Swap ⟨3, by decide⟩),
   opAt 35 .ADD,
   opAt 36 .MSTORE,
   pushAt 37 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 38 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel
