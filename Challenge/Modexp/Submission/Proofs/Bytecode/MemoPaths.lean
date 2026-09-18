import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
set_option warningAsError true
set_option maxRecDepth 400000
set_option maxHeartbeats 2000000

/-!
# Located instructions of the fixed-vector memo

The recogniser occupies bytes 5251..5283, which the inherited image used as
padding that no input can reach; the two bytes at 5284..5285 are left as they
were.  The answer block is the only appended code, at 5428..5438.

The recogniser is entered from the retargeted dispatch jump with the stack
`[m, e, b]` that the pc-570 dispatcher expects, so a miss restores that
dispatcher by changing only the program counter.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Memo

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

/-- The recognition prefix: eighteen instructions ending in the miss branch. -/
def guardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4205 .JUMPDEST,
   opAt 4206 (.Dup ⟨2, by decide⟩),
   pushAt 4207 1 1,
   opAt 4208 .SUB,
   pushAt 4209 5 137506062208,
   pushAt 4210 1 68,
   opAt 4211 .CALLDATALOAD,
   opAt 4212 .SUB,
   opAt 4213 .OR,
   pushAt 4214 1 100,
   opAt 4215 .CALLDATALOAD,
   opAt 4216 .OR,
   opAt 4217 (.Dup ⟨2, by decide⟩),
   pushAt 4218 1 2,
   opAt 4219 .SUB,
   opAt 4220 .OR,
   pushAt 4221 2 570,
   opAt 4222 .JUMPI]

/-- On a match the recogniser jumps to the appended answer block. -/
def hitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4223 (.Dup ⟨0, by decide⟩),
   pushAt 4224 2 5428,
   opAt 4225 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4345 .JUMPDEST,
   pushAt 4346 2 65535,
   pushAt 4347 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4349 0 0,
   opAt 4350 .MSTORE,
   pushAt 4351 0 0,
   opAt 4352 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 4348 .EXP

@[simp] theorem guardPCs (i : Nat) (hi : 4205 ≤ i) (hii : i ≤ 4225) :
    Artifact.submissionArtifact.instructionPC i =
      ([5251,5252,5253,5255,5256,5262,5264,5265,5266,5267,5269,5270,5271,5272,
        5274,5275,5276,5279,5280,5281,5284] : List Nat)[i - 4205]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 4345 ≤ i) (hii : i ≤ 4352) :
    Artifact.submissionArtifact.instructionPC i =
      ([5428,5429,5432,5434,5435,5436,5437,5438] : List Nat)[i - 4345]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
