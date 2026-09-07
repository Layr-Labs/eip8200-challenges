import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def startIndex : Nat := 2950

/-- A bounded, cached instruction slice.  This keeps concrete reduction local. -/
private def template : List Instr :=
    [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .push 1 32, .op (.Dup ⟨3, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨3, by decide⟩), .op .ADD, .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

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
    Artifact.submissionArtifact.instructionPC startIndex = 4796 := by
  rfl

@[simp] theorem peelPC (index : Nat) (hlo : startIndex ≤ index)
    (hhi : index ≤ 2994) :
    Artifact.submissionArtifact.instructionPC index =
            [4796, 4797, 4798, 4799, 4832, 4833, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841,
       4842, 4843, 4844, 4845, 4846, 4847, 4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855,
       4856, 4857, 4858, 4859, 4861, 4862, 4895, 4896, 4897, 4898, 4899, 4932, 4933, 4934,
       4935, 4936, 4937][index - startIndex]! := by
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

/-- Instructions 2950..2994, pc 4796..4937. -/
def cios2L2Peel :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
    [opAt 0 .JUMPDEST, opAt 1 (.Dup ⟨0, by decide⟩), opAt 2 .MLOAD,
   pushAt 3 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   opAt 4 (.Dup ⟨5, by decide⟩), opAt 5 (.Dup ⟨2, by decide⟩), opAt 6 .MUL,
   opAt 7 (.Swap ⟨1, by decide⟩), opAt 8 (.Dup ⟨6, by decide⟩), opAt 9 .MULMOD,
   opAt 10 (.Dup ⟨1, by decide⟩), opAt 11 (.Dup ⟨1, by decide⟩), opAt 12 .LT, opAt 13 .SUB,
   opAt 14 (.Dup ⟨4, by decide⟩), opAt 15 (.Dup ⟨2, by decide⟩), opAt 16 .ADD,
   opAt 17 (.Dup ⟨0, by decide⟩), opAt 18 (.Swap ⟨5, by decide⟩), opAt 19 .GT, opAt 20 .SUB,
   opAt 21 .SUB, opAt 22 (.Dup ⟨3, by decide⟩), opAt 23 (.Dup ⟨3, by decide⟩), opAt 24 .MLOAD,
   opAt 25 .ADD, opAt 26 (.Dup ⟨0, by decide⟩), opAt 27 (.Swap ⟨4, by decide⟩), opAt 28 .GT,
   opAt 29 .ADD, opAt 30 (.Swap ⟨2, by decide⟩), pushAt 31 1 32,
   opAt 32 (.Dup ⟨3, by decide⟩),
   pushAt 33 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 34 .ADD, opAt 35 (.Swap ⟨3, by decide⟩), opAt 36 .ADD, opAt 37 .MSTORE,
   pushAt 38 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   opAt 39 .ADD, opAt 40 .JUMPDEST, opAt 41 .JUMPDEST, opAt 42 .JUMPDEST, opAt 43 .JUMPDEST,
   opAt 44 .JUMPDEST]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel
