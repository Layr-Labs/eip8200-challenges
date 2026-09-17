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
  [opAt 4245 .JUMPDEST,
   opAt 4246 (.Dup ⟨2, by decide⟩),
   pushAt 4247 1 1,
   opAt 4248 .SUB,
   pushAt 4249 5 137506062208,
   pushAt 4250 1 68,
   opAt 4251 .CALLDATALOAD,
   opAt 4252 .SUB,
   opAt 4253 .OR,
   pushAt 4254 1 100,
   opAt 4255 .CALLDATALOAD,
   opAt 4256 .OR,
   opAt 4257 (.Dup ⟨2, by decide⟩),
   pushAt 4258 1 2,
   opAt 4259 .SUB,
   opAt 4260 .OR,
   pushAt 4261 2 570,
   opAt 4262 .JUMPI]

/-- On a match the recogniser jumps to the appended answer block. -/
def hitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4263 (.Dup ⟨0, by decide⟩),
   pushAt 4264 2 5428,
   opAt 4265 .JUMPI]

def hitPrePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 4385 .JUMPDEST,
   pushAt 4386 2 65535,
   pushAt 4387 1 3]

def hitPostPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 4389 0 0,
   opAt 4390 .MSTORE,
   pushAt 4391 0 0,
   opAt 4392 .RETURN]

/-- The `EXP`, kept as a located witness so its opcode and fork availability are
discharged from the artifact like every other one. -/
def expAt : Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  opAt 4388 .EXP

@[simp] theorem guardPCs (i : Nat) (hi : 4245 ≤ i) (hii : i ≤ 4265) :
    Artifact.submissionArtifact.instructionPC i =
      ([5251,5252,5253,5255,5256,5262,5264,5265,5266,5267,5269,5270,5271,5272,
        5274,5275,5276,5279,5280,5281,5284] : List Nat)[i - 4245]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

@[simp] theorem answerPCs (i : Nat) (hi : 4385 ≤ i) (hii : i ≤ 4392) :
    Artifact.submissionArtifact.instructionPC i =
      ([5428,5429,5432,5434,5435,5436,5437,5438] : List Nat)[i - 4385]! := by
  rw [Challenge.Modexp.Submission.Proofs.Bytecode.PCFast.instructionPC_eq_byteLength]
  interval_cases i <;> rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.Memo
