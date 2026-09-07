import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2866

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨1, by decide⟩),
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
   .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨4, by decide⟩),
   .op .LT,
   .op .ADD,
   .op (.Swap ⟨2, by decide⟩),
   .op (.Dup ⟨2, by decide⟩),
   .push 1 32,
   .op .ADD,
   .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD,
   .op (.Swap ⟨0, by decide⟩)]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4520 := by
  rfl

@[simp] theorem peelPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 2910) :
    Artifact.submissionArtifact.instructionPC index =
      [4520, 4521, 4522, 4523, 4524, 4525, 4526, 4527, 4528,
       4561, 4562, 4563, 4564, 4565, 4566, 4567, 4568, 4569,
       4570, 4571, 4572, 4573, 4574, 4575, 4576, 4577, 4578,
       4579, 4580, 4581, 4582, 4583, 4584, 4585, 4586, 4587,
       4588, 4590, 4591, 4592, 4625, 4626, 4627, 4660,
       4661][index - startIndex]! := by
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

/-- Instructions 2866..2910, pc 4520..4661. -/
def cios2L2Peel :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 0 .JUMPDEST,
   opAt 1 (.Dup ⟨3, by decide⟩),
   opAt 2 (.Dup ⟨1, by decide⟩),
   opAt 3 .MLOAD,
   opAt 4 (.Dup ⟨1, by decide⟩),
   opAt 5 (.Dup ⟨1, by decide⟩),
   opAt 6 .MUL,
   opAt 7 (.Swap ⟨1, by decide⟩),
   pushAt 8 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 9 (.Swap ⟨1, by decide⟩),
   opAt 10 .MULMOD,
   opAt 11 (.Dup ⟨1, by decide⟩),
   opAt 12 (.Dup ⟨1, by decide⟩),
   opAt 13 .LT,
   opAt 14 (.Dup ⟨2, by decide⟩),
   opAt 15 .ADD,
   opAt 16 (.Swap ⟨0, by decide⟩),
   opAt 17 .SUB,
   opAt 18 (.Dup ⟨3, by decide⟩),
   opAt 19 .MLOAD,
   opAt 20 (.Swap ⟨1, by decide⟩),
   opAt 21 (.Dup ⟨2, by decide⟩),
   opAt 22 .ADD,
   opAt 23 (.Swap ⟨1, by decide⟩),
   opAt 24 (.Dup ⟨2, by decide⟩),
   opAt 25 .LT,
   opAt 26 .ADD,
   opAt 27 (.Swap ⟨0, by decide⟩),
   opAt 28 (.Dup ⟨4, by decide⟩),
   opAt 29 .ADD,
   opAt 30 (.Swap ⟨3, by decide⟩),
   opAt 31 (.Dup ⟨4, by decide⟩),
   opAt 32 .LT,
   opAt 33 .ADD,
   opAt 34 (.Swap ⟨2, by decide⟩),
   opAt 35 (.Dup ⟨2, by decide⟩),
   pushAt 36 1 32,
   opAt 37 .ADD,
   opAt 38 .MSTORE,
   pushAt 39 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 40 .ADD,
   opAt 41 (.Swap ⟨0, by decide⟩),
   pushAt 42 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 43 .ADD,
   opAt 44 (.Swap ⟨0, by decide⟩)]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel
