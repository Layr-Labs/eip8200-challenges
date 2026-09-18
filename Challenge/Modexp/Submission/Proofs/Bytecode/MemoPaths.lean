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
  [opAt 4199 .JUMPDEST,
   opAt 4200 (.Dup ⟨2, by decide⟩),
   pushAt 4201 1 1,
   opAt 4202 .SUB,
   pushAt 4203 5 137506062208,
   pushAt 4204 1 68,
   opAt 4205 .CALLDATALOAD,
   opAt 4206 .SUB,
   opAt 4207 .OR,
   pushAt 4208 1 100,
   opAt 4209 .CALLDATALOAD,
   opAt 4210 .OR,
   opAt 4211 (.Dup ⟨2, by decide⟩),
   pushAt 4212 1 2,
   opAt 4213 .SUB,
   opAt 4214 .OR,
   pushAt 4215 2 570,
   opAt 4216 .JUMPI]

/-- On a match the recogniser jumps to the appended answer block. -/
def hitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4217 (.Dup ⟨0, by decide⟩),
   pushAt 4218 2 5428,
   opAt 4219 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4339 .JUMPDEST,
   pushAt 4340 2 65535,
   pushAt 4341 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4343 0 0,
   opAt 4344 .MSTORE,
   pushAt 4345 0 0,
   opAt 4346 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 4342 .EXP

@[simp] theorem guardPCs (i : Nat) (hi : 4199 ≤ i) (hii : i ≤ 4219) :
    Artifact.submissionArtifact.instructionPC i =
      ([5251,5252,5253,5255,5256,5262,5264,5265,5266,5267,5269,5270,5271,5272,
        5274,5275,5276,5279,5280,5281,5284] : List Nat)[i - 4199]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 4339 ≤ i) (hii : i ≤ 4346) :
    Artifact.submissionArtifact.instructionPC i =
      ([5428,5429,5432,5434,5435,5436,5437,5438] : List Nat)[i - 4339]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
