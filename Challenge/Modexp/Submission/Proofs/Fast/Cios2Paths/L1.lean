import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

def firstStartIndex : Nat := 2726

private def firstTemplate : List Instr :=
    [.op .JUMPDEST, .op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op .MSTORE,
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
    Artifact.submissionArtifact.instructionPC firstStartIndex = 4136 := by
  rfl

@[simp] theorem firstPC (index : Nat) (hlo : firstStartIndex ≤ index)
    (hhi : index ≤ 2763) :
    Artifact.submissionArtifact.instructionPC index =
            [4136, 4137, 4138, 4139, 4172, 4173, 4174, 4175, 4176, 4177, 4178, 4179, 4180, 4181,
       4182, 4183, 4184, 4185, 4186, 4187, 4188, 4189, 4190, 4191, 4192, 4193, 4194, 4195,
       4196, 4197, 4198, 4199, 4200, 4233, 4234, 4235, 4236, 4269][index - firstStartIndex]! := by
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

/-- First MAC: instructions 2726..2768, pc 4136..4274. -/
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
   firstOpAt 29 .ADD, firstOpAt 30 (.Swap ⟨2, by decide⟩), firstOpAt 31 (.Dup ⟨2, by decide⟩),
   firstPushAt 32 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 33 .ADD, firstOpAt 34 (.Swap ⟨2, by decide⟩), firstOpAt 35 .MSTORE,
   firstPushAt 36 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   firstOpAt 37 .ADD]

def secondStartIndex : Nat := 2764

private def secondTemplate : List Instr :=
    [.op (.Dup ⟨0, by decide⟩), .op .MLOAD,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639935,
   .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL, .op (.Swap ⟨1, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op .MULMOD, .op (.Dup ⟨1, by decide⟩),
   .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB, .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨2, by decide⟩), .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB, .op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op .MLOAD, .op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩), .op .GT,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩),
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Swap ⟨2, by decide⟩), .op .MSTORE,
   .push 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   .op .ADD, .op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .GT, .push 2 4136,
   .op .JUMPI, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST,
   .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST, .op .JUMPDEST]

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
    Artifact.submissionArtifact.instructionPC secondStartIndex = 4270 := by
  rfl

@[simp] theorem secondPC (index : Nat) (hlo : secondStartIndex ≤ index)
    (hhi : index ≤ 2815) :
    Artifact.submissionArtifact.instructionPC index =
            [4270, 4271, 4272, 4305, 4306, 4307, 4308, 4309, 4310, 4311, 4312, 4313, 4314, 4315,
       4316, 4317, 4318, 4319, 4320, 4321, 4322, 4323, 4324, 4325, 4326, 4327, 4328, 4329,
       4330, 4331, 4332, 4333, 4366, 4367, 4368, 4369, 4402, 4403, 4404, 4405, 4406, 4409,
       4410, 4411, 4412, 4413, 4414, 4415, 4416, 4417, 4418, 4419][index - secondStartIndex]! := by
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

/-- Second MAC and pair test: instructions 2769..2815, pc 4270..4419. -/
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
   secondOpAt 30 (.Dup ⟨2, by decide⟩),
   secondPushAt 31 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 32 .ADD, secondOpAt 33 (.Swap ⟨2, by decide⟩), secondOpAt 34 .MSTORE,
   secondPushAt 35 32 115792089237316195423570985008687907853269984665640564039457584007913129639904,
   secondOpAt 36 .ADD, secondOpAt 37 (.Dup ⟨5, by decide⟩),
   secondOpAt 38 (.Dup ⟨1, by decide⟩), secondOpAt 39 .GT, secondPushAt 40 2 4136,
   secondOpAt 41 .JUMPI]

/-- Same trace plus the ten padding `JUMPDEST`s on the fall-through path. -/
def secondMacExit :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  secondMac ++
  [secondOpAt 42 .JUMPDEST,
   secondOpAt 43 .JUMPDEST,
   secondOpAt 44 .JUMPDEST,
   secondOpAt 45 .JUMPDEST,
   secondOpAt 46 .JUMPDEST,
   secondOpAt 47 .JUMPDEST,
   secondOpAt 48 .JUMPDEST,
   secondOpAt 49 .JUMPDEST,
   secondOpAt 50 .JUMPDEST,
   secondOpAt 51 .JUMPDEST]


/-- The complete pair block, retained for whole-block consumers. -/
def cios2L1 := firstMac ++ secondMac

end Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1
