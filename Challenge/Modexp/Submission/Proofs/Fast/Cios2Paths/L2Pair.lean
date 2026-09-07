import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def firstStartIndex : Nat := 2911

private def firstTemplate : List Instr :=
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
   .op .ADD]

private theorem firstSlice_eq :
    (Artifact.submissionInstructions.drop firstStartIndex).take
        firstTemplate.length = firstTemplate := by
  rfl

private theorem firstGetElem (offset : Nat)
    (hoffset : offset < firstTemplate.length) :
    Artifact.submissionInstructions[firstStartIndex + offset]? =
      firstTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) firstSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem firstStartPC :
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4662 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 2950) :
    Artifact.submissionArtifact.instructionPC index =
            [4662, 4663, 4664, 4665, 4698, 4699, 4700, 4701, 4702, 4703, 4704, 4705, 4706, 4707,
       4708, 4709, 4710, 4711, 4712, 4713, 4714, 4715, 4716, 4717, 4718, 4719, 4720, 4721,
       4722, 4723, 4724, 4725, 4727, 4728, 4761, 4762, 4763, 4764, 4765, 4798][index - firstStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (firstStartIndex + (index - firstStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC firstStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop firstStartIndex).take
              (index - firstStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact firstStartIndex
        (index - firstStartIndex)
    _ = _ := by
      rw [firstStartPC]
      interval_cases index <;> rfl

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
  ⟨firstStartIndex + offset, .push width value,
    (firstGetElem offset hoffset).trans hget, hwf⟩

/-- First MAC: instructions 2911..2955, pc 4662..4803. -/
def firstMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
    [firstOpAt 0 .JUMPDEST, firstOpAt 1 (.Dup ⟨0, by decide⟩), firstOpAt 2 .MLOAD,
   firstPushAt 3 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   firstOpAt 4 (.Dup ⟨5, by decide⟩), firstOpAt 5 (.Dup ⟨2, by decide⟩), firstOpAt 6 .MUL,
   firstOpAt 7 (.Swap ⟨1, by decide⟩), firstOpAt 8 (.Dup ⟨6, by decide⟩), firstOpAt 9 .MULMOD,
   firstOpAt 10 (.Dup ⟨1, by decide⟩), firstOpAt 11 (.Dup ⟨1, by decide⟩), firstOpAt 12 .LT,
   firstOpAt 13 .SUB, firstOpAt 14 (.Dup ⟨4, by decide⟩), firstOpAt 15 (.Dup ⟨2, by decide⟩),
   firstOpAt 16 .ADD, firstOpAt 17 (.Dup ⟨0, by decide⟩), firstOpAt 18 (.Swap ⟨5, by decide⟩),
   firstOpAt 19 .GT, firstOpAt 20 .SUB, firstOpAt 21 .SUB, firstOpAt 22 (.Dup ⟨3, by decide⟩),
   firstOpAt 23 (.Dup ⟨3, by decide⟩), firstOpAt 24 .MLOAD, firstOpAt 25 .ADD,
   firstOpAt 26 (.Dup ⟨0, by decide⟩), firstOpAt 27 (.Swap ⟨4, by decide⟩), firstOpAt 28 .GT,
   firstOpAt 29 .ADD, firstOpAt 30 (.Swap ⟨2, by decide⟩), firstPushAt 31 1 32,
   firstOpAt 32 (.Dup ⟨3, by decide⟩),
   firstPushAt 33 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 34 .ADD, firstOpAt 35 (.Swap ⟨3, by decide⟩), firstOpAt 36 .ADD,
   firstOpAt 37 .MSTORE,
   firstPushAt 38 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 39 .ADD]

def secondStartIndex : Nat := 2951

private def secondTemplate : List Instr :=
    [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
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
   .op .ADD, .push 2 8224, .op (.Dup ⟨2, by decide⟩), .op .GT, .push 2 4662, .op .JUMPI,
   .push 8 0, .op .POP]

private theorem secondSlice_eq :
    (Artifact.submissionInstructions.drop secondStartIndex).take
        secondTemplate.length = secondTemplate := by
  rfl

private theorem secondGetElem (offset : Nat)
    (hoffset : offset < secondTemplate.length) :
    Artifact.submissionInstructions[secondStartIndex + offset]? =
      secondTemplate[offset]? := by
  have hs := congrArg (fun xs : List Instr => xs[offset]?) secondSlice_eq
  rw [List.getElem?_take, if_pos hoffset, List.getElem?_drop] at hs
  simpa [Nat.add_comm] using hs

private theorem secondStartPC :
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4799 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 2996) :
    Artifact.submissionArtifact.instructionPC index =
            [4799, 4800, 4801, 4834, 4835, 4836, 4837, 4838, 4839, 4840, 4841, 4842, 4843, 4844,
       4845, 4846, 4847, 4848, 4849, 4850, 4851, 4852, 4853, 4854, 4855, 4856, 4857, 4858,
       4859, 4860, 4861, 4863, 4864, 4897, 4898, 4899, 4900, 4901, 4934, 4935, 4938, 4939,
       4940, 4943, 4944, 4953][index - secondStartIndex]! := by
  calc
    Artifact.submissionArtifact.instructionPC index =
        Artifact.submissionArtifact.instructionPC
          (secondStartIndex + (index - secondStartIndex)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC secondStartIndex +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop secondStartIndex).take
              (index - secondStartIndex))).length :=
      instructionPC_add Artifact.submissionArtifact secondStartIndex
        (index - secondStartIndex)
    _ = _ := by
      rw [secondStartPC]
      interval_cases index <;> rfl

def secondOpAt (offset : Nat) (op : Operation)
    (hget : secondTemplate[offset]? = some (.op op) := by rfl)
    (hoffset : offset < secondTemplate.length := by decide)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨secondStartIndex + offset, .op op, (secondGetElem offset hoffset).trans hget,
    wfOp hopcode hplain havailable⟩

def secondPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hget : secondTemplate[offset]? = some (.push width value) := by rfl)
    (hoffset : offset < secondTemplate.length := by decide)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨secondStartIndex + offset, .push width value,
    (secondGetElem offset hoffset).trans hget, hwf⟩

/-- Second MAC and pair test: instructions 2951..2994, pc 4799..4943. -/
def secondMac :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
    [secondOpAt 0 (.Dup ⟨0, by decide⟩), secondOpAt 1 .MLOAD,
   secondPushAt 2 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   secondOpAt 3 (.Dup ⟨5, by decide⟩), secondOpAt 4 (.Dup ⟨2, by decide⟩), secondOpAt 5 .MUL,
   secondOpAt 6 (.Swap ⟨1, by decide⟩), secondOpAt 7 (.Dup ⟨6, by decide⟩),
   secondOpAt 8 .MULMOD, secondOpAt 9 (.Dup ⟨1, by decide⟩),
   secondOpAt 10 (.Dup ⟨1, by decide⟩), secondOpAt 11 .LT, secondOpAt 12 .SUB,
   secondOpAt 13 (.Dup ⟨4, by decide⟩), secondOpAt 14 (.Dup ⟨2, by decide⟩),
   secondOpAt 15 .ADD, secondOpAt 16 (.Dup ⟨0, by decide⟩),
   secondOpAt 17 (.Swap ⟨5, by decide⟩), secondOpAt 18 .GT, secondOpAt 19 .SUB,
   secondOpAt 20 .SUB, secondOpAt 21 (.Dup ⟨3, by decide⟩),
   secondOpAt 22 (.Dup ⟨3, by decide⟩), secondOpAt 23 .MLOAD, secondOpAt 24 .ADD,
   secondOpAt 25 (.Dup ⟨0, by decide⟩), secondOpAt 26 (.Swap ⟨4, by decide⟩),
   secondOpAt 27 .GT, secondOpAt 28 .ADD, secondOpAt 29 (.Swap ⟨2, by decide⟩),
   secondPushAt 30 1 32, secondOpAt 31 (.Dup ⟨3, by decide⟩),
   secondPushAt 32 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 33 .ADD, secondOpAt 34 (.Swap ⟨3, by decide⟩), secondOpAt 35 .ADD,
   secondOpAt 36 .MSTORE,
   secondPushAt 37 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 38 .ADD, secondPushAt 39 2 8224, secondOpAt 40 (.Dup ⟨2, by decide⟩),
   secondOpAt 41 .GT, secondPushAt 42 2 4662, secondOpAt 43 .JUMPI]

/-- Same trace plus the final identity `PUSH8 0`/`POP` at instructions 2995..2996, pc 4944..4953. -/
def secondMacExit :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  secondMac ++
  [secondPushAt 44 8 0,
   secondOpAt 45 .POP]


/-- The complete pair block, retained for whole-block consumers. -/
def cios2L2Pair := firstMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L2Pair
