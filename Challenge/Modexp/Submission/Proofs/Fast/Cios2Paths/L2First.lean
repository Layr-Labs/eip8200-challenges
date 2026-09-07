import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def firstStartIndex : Nat := 3122

private def firstTemplate : List Instr :=
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
   .op (.Dup ⟨11, by decide⟩),
   .op .ADD,
   .op (.Swap ⟨3, by decide⟩),
   .op .ADD,
   .op .MSTORE,
   .op (.Dup ⟨8, by decide⟩),
   .op .ADD]

private theorem slice_eq :
    (Artifact.submissionInstructions.drop firstStartIndex).take firstTemplate.length = firstTemplate := by
  rfl

private theorem firstGetElem (offset : Nat) (hoffset : offset < firstTemplate.length) :
    Artifact.submissionInstructions[firstStartIndex + offset]? = firstTemplate[offset]? := by
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
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4905 := by rfl

@[simp] theorem firstPC (i : Nat) (hi : firstStartIndex ≤ i) (hii : i ≤ 3161) :
    Artifact.submissionArtifact.instructionPC i =
      [4905, 4906, 4907, 4908, 4941, 4942, 4943, 4944, 4945, 4946, 4947, 4948, 4949, 4950, 4951, 4952, 4953, 4954, 4955, 4956, 4957, 4958, 4959, 4960, 4961, 4962, 4963, 4964, 4965, 4966, 4967, 4968, 4970, 4971, 4972, 4973, 4974, 4975, 4976, 4977][i - firstStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (firstStartIndex + (i - firstStartIndex)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC firstStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop firstStartIndex).take
              (i - firstStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact firstStartIndex (i - firstStartIndex)
    _ = _ := by
      rw [startPC]
      interval_cases i <;> rfl

def firstOpAt (offset : Nat) (op : Operation)
    (hget : firstTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < firstTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨firstStartIndex + offset, .op op, (firstGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def firstPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : firstTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < firstTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨firstStartIndex + offset, .push width value, (firstGetElem offset hoffset).trans hget, hwf⟩

/-- Exact live instruction slice 3122..3161, PCs 4905..4977. -/
def firstMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [firstOpAt 0 .JUMPDEST,
   firstOpAt 1 (.Dup ⟨0, by decide⟩),
   firstOpAt 2 .MLOAD,
   firstPushAt 3 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   firstOpAt 4 (.Dup ⟨5, by decide⟩),
   firstOpAt 5 (.Dup ⟨2, by decide⟩),
   firstOpAt 6 .MUL,
   firstOpAt 7 (.Swap ⟨1, by decide⟩),
   firstOpAt 8 (.Dup ⟨6, by decide⟩),
   firstOpAt 9 .MULMOD,
   firstOpAt 10 (.Dup ⟨1, by decide⟩),
   firstOpAt 11 (.Dup ⟨1, by decide⟩),
   firstOpAt 12 .LT,
   firstOpAt 13 .SUB,
   firstOpAt 14 (.Dup ⟨4, by decide⟩),
   firstOpAt 15 (.Dup ⟨2, by decide⟩),
   firstOpAt 16 .ADD,
   firstOpAt 17 (.Dup ⟨0, by decide⟩),
   firstOpAt 18 (.Swap ⟨5, by decide⟩),
   firstOpAt 19 .GT,
   firstOpAt 20 .SUB,
   firstOpAt 21 .SUB,
   firstOpAt 22 (.Dup ⟨3, by decide⟩),
   firstOpAt 23 (.Dup ⟨3, by decide⟩),
   firstOpAt 24 .MLOAD,
   firstOpAt 25 .ADD,
   firstOpAt 26 (.Dup ⟨0, by decide⟩),
   firstOpAt 27 (.Swap ⟨4, by decide⟩),
   firstOpAt 28 .GT,
   firstOpAt 29 .ADD,
   firstOpAt 30 (.Swap ⟨2, by decide⟩),
   firstPushAt 31 1 32,
   firstOpAt 32 (.Dup ⟨3, by decide⟩),
   firstOpAt 33 (.Dup ⟨11, by decide⟩),
   firstOpAt 34 .ADD,
   firstOpAt 35 (.Swap ⟨3, by decide⟩),
   firstOpAt 36 .ADD,
   firstOpAt 37 .MSTORE,
   firstOpAt 38 (.Dup ⟨8, by decide⟩),
   firstOpAt 39 .ADD]

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
