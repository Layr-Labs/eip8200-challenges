import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
set_option warningAsError true
set_option maxRecDepth 10000

/-!
# Wide-modulus dispatch

The header dispatcher tests `32 < modulusSize` and, when it holds, jumps
straight to the compact multi-limb fallback at pc 236 with the five header
words still live.  `modexpBig` re-reads the sizes from calldata and tolerates
any incoming stack, so no trampoline frame is built any more.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def bigJumpPath := Dispatch.wordJumpPath

def bigCheckExpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 402 .JUMPDEST,
   opAt 403 (.Dup ⟨2, by decide⟩),
   pushAt 404 1 96,
   opAt 405 .ADD]

def bigCheckModPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 406 (.Dup ⟨2, by decide⟩),
   opAt 407 (.Dup ⟨1, by decide⟩),
   opAt 408 .ADD]

def bigCheckComparePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 409 1 32,
   opAt 410 (.Dup ⟨3, by decide⟩),
   opAt 411 .GT]

/-- `PUSH1 236; JUMPI` (pc 580..582): the taken branch is the fallback entry itself. -/
def bigCheckJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 412 1 238,
   opAt 413 .JUMPI]

def bigCheckPath := bigCheckExpPath ++ bigCheckModPath ++
  bigCheckComparePath ++ bigCheckJumpPath

def bigExpOffsetState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 575
    stack := [UInt256.ofNat (96 + baseSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def bigOffsetsState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 578
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigComparedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 582
    stack := [1, UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Calling-convention state at the first instruction of `modexpBig` (pc 236): the
header dispatcher's taken `JUMPI` lands here with the five header words
`[modOff, expOff, msize, esize, bsize]` still live. -/
def bigEntryState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 238
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- The dispatcher's exit state is the fallback's entry state. -/
abbrev bigCheckedState (input : ByteArray) : State := bigEntryState input

theorem jump704 : Decode.isValidJumpDest submissionBytecode 238 = true :=
  Artifact.isValidJumpDest_index 165 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
