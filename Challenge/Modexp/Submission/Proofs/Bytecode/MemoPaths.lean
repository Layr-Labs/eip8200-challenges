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
  [opAt 4241 .JUMPDEST,
   opAt 4242 (.Dup ⟨2, by decide⟩),
   pushAt 4243 1 1,
   opAt 4244 .SUB,
   pushAt 4245 5 137506062208,
   pushAt 4246 1 68,
   opAt 4247 .CALLDATALOAD,
   opAt 4248 .SUB,
   opAt 4249 .OR,
   pushAt 4250 1 100,
   opAt 4251 .CALLDATALOAD,
   opAt 4252 .OR,
   opAt 4253 (.Dup ⟨2, by decide⟩),
   pushAt 4254 1 2,
   opAt 4255 .SUB,
   opAt 4256 .OR,
   pushAt 4257 2 570,
   opAt 4258 .JUMPI]

/-- On a match the recogniser jumps to the appended answer block. -/
def hitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4259 (.Dup ⟨0, by decide⟩),
   pushAt 4260 2 5424,
   opAt 4261 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4381 .JUMPDEST,
   pushAt 4382 2 65535,
   pushAt 4383 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4385 0 0,
   opAt 4386 .MSTORE,
   pushAt 4387 0 0,
   opAt 4388 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 4384 .EXP

@[simp] theorem guardPCs (i : Nat) (hi : 4245 ≤ i) (hii : i ≤ 4261) :
    Artifact.submissionArtifact.instructionPC i =
      ([5251,5252,5249,5251,5252,5262,5260,5265,5266,5267,5265,5270,5271,5272,
        5270,5275,5276,5275,5280,5281,5280] : List Nat)[i - 4245]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 4381 ≤ i) (hii : i ≤ 4392) :
    Artifact.submissionArtifact.instructionPC i =
      ([5428,5425,5432,5434,5431,5432,5433,5434] : List Nat)[i - 4381]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
