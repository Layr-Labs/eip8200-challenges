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
  [opAt 4213 .JUMPDEST,
   opAt 4214 (.Dup ⟨2, by decide⟩),
   pushAt 4215 1 1,
   opAt 4216 .SUB,
   pushAt 4217 5 137506062208,
   pushAt 4218 1 68,
   opAt 4219 .CALLDATALOAD,
   opAt 4220 .SUB,
   opAt 4221 .OR,
   pushAt 4222 1 100,
   opAt 4223 .CALLDATALOAD,
   opAt 4224 .OR,
   opAt 4225 (.Dup ⟨2, by decide⟩),
   pushAt 4226 1 2,
   opAt 4227 .SUB,
   opAt 4228 .OR,
   pushAt 4229 2 570,
   opAt 4230 .JUMPI]

/-- On a match the recogniser jumps to the appended answer block. -/
def hitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4231 (.Dup ⟨0, by decide⟩),
   pushAt 4232 2 5433,
   opAt 4233 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4352 .JUMPDEST,
   pushAt 4353 2 65535,
   pushAt 4354 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4356 0 0,
   opAt 4357 .MSTORE,
   pushAt 4358 0 0,
   opAt 4359 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 4355 .EXP

@[simp] theorem guardPCs (i : Nat) (hi : 4213 ≤ i) (hii : i ≤ 4233) :
    Artifact.submissionArtifact.instructionPC i =
      ([5261,5262,5263,5265,5266,5272,5274,5275,5276,5277,5279,5280,5281,5282,
        5284,5285,5286,5289,5290,5291,5294] : List Nat)[i - 4213]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 4352 ≤ i) (hii : i ≤ 4359) :
    Artifact.submissionArtifact.instructionPC i =
      ([5433,5434,5437,5439,5440,5441,5442,5443] : List Nat)[i - 4352]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
