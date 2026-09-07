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

def peelStartIndex : Nat := 2930

private def peelTemplate : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨0, by decide⟩),
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
    Artifact.submissionArtifact.instructionPC peelStartIndex = 4776 := by
  rfl

@[simp] theorem peelPC (index : Nat) (hlo : peelStartIndex ≤ index)
    (hhi : index ≤ 2969) :
    Artifact.submissionArtifact.instructionPC index =
      [4776,4777,4778,4779,4812,4813,4814,4815,4816,4817,4818,4819,4820,4821,4822,4823,4824,4825,4826,4827,4828,4829,4830,4831,4832,4833,4834,4835,4836,4837,4838,4839,4841,4842,4875,4876,4877,4878,4879,4912][index - peelStartIndex]! := by
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

/-- Peeled L2 MAC: instructions 2930..2969, pc 4776..4912. -/
def cios2L2Peel :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [peelOpAt 0 .JUMPDEST,
   peelOpAt 1 (.Dup ⟨0, by decide⟩),
   peelOpAt 2 .MLOAD,
   peelPushAt 3 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   peelOpAt 4 (.Dup ⟨5, by decide⟩),
   peelOpAt 5 (.Dup ⟨2, by decide⟩),
   peelOpAt 6 .MUL,
   peelOpAt 7 (.Swap ⟨1, by decide⟩),
   peelOpAt 8 (.Dup ⟨6, by decide⟩),
   peelOpAt 9 .MULMOD,
   peelOpAt 10 (.Dup ⟨1, by decide⟩),
   peelOpAt 11 (.Dup ⟨1, by decide⟩),
   peelOpAt 12 .LT,
   peelOpAt 13 .SUB,
   peelOpAt 14 (.Dup ⟨4, by decide⟩),
   peelOpAt 15 (.Dup ⟨2, by decide⟩),
   peelOpAt 16 .ADD,
   peelOpAt 17 (.Dup ⟨0, by decide⟩),
   peelOpAt 18 (.Swap ⟨5, by decide⟩),
   peelOpAt 19 .GT,
   peelOpAt 20 .SUB,
   peelOpAt 21 .SUB,
   peelOpAt 22 (.Dup ⟨3, by decide⟩),
   peelOpAt 23 (.Dup ⟨3, by decide⟩),
   peelOpAt 24 .MLOAD,
   peelOpAt 25 .ADD,
   peelOpAt 26 (.Dup ⟨0, by decide⟩),
   peelOpAt 27 (.Swap ⟨4, by decide⟩),
   peelOpAt 28 .GT,
   peelOpAt 29 .ADD,
   peelOpAt 30 (.Swap ⟨2, by decide⟩),
   peelPushAt 31 1 32,
   peelOpAt 32 (.Dup ⟨3, by decide⟩),
   peelPushAt 33 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   peelOpAt 34 .ADD,
   peelOpAt 35 (.Swap ⟨3, by decide⟩),
   peelOpAt 36 .ADD,
   peelOpAt 37 .MSTORE,
   peelPushAt 38 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   peelOpAt 39 .ADD]


end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Peel
