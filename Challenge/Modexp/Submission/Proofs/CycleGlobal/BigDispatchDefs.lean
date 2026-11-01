import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Dispatch
noncomputable section
set_option warningAsError true
set_option maxRecDepth 10000

/-!
# Wide-modulus dispatch

The header dispatcher tests `32 < modulusSize` and, when it holds, jumps
straight to the compact multi-limb fallback at pc 236 with the five header
words still live.  `modexpBig` re-reads the sizes from calldata and tolerates
any incoming stack, so no trampoline frame is built any more.
-/

namespace CycleSubmission.Global.BigDispatch
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : CycleSubmission.Artifact.instructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def bigJumpPath := Dispatch.wordJumpPath

def bigCheckExpPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 383 .JUMPDEST,
   opAt 384 (.Dup ⟨2, by decide⟩),
   pushAt 385 1 96,
   opAt 386 .ADD]

def bigCheckModPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [opAt 387 (.Dup ⟨2, by decide⟩),
   opAt 388 (.Dup ⟨1, by decide⟩),
   opAt 389 .ADD]

def bigCheckComparePath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 390 1 32,
   opAt 391 (.Dup ⟨3, by decide⟩),
   opAt 392 .GT]

/-- `PUSH1 236; JUMPI` (pc 580..582): the taken branch is the fallback entry itself. -/
def bigCheckJumpPath :
    List (Challenge.EvmProof.Stepper.Located CycleSubmission.Artifact.artifact .Osaka) :=
  [pushAt 393 1 219,
   opAt 394 .JUMPI]

def bigCheckPath := bigCheckExpPath ++ bigCheckModPath ++
  bigCheckComparePath ++ bigCheckJumpPath

def bigExpOffsetState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 555
    stack := [UInt256.ofNat (96 + baseSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def bigOffsetsState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 558
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigComparedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 562
    stack := [1, UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- Calling-convention state at the first instruction of `modexpBig` (pc 236): the
header dispatcher's taken `JUMPI` lands here with the five header words
`[modOff, expOff, msize, esize, bsize]` still live. -/
def bigEntryState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 219
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

/-- The dispatcher's exit state is the fallback's entry state. -/
abbrev bigCheckedState (input : ByteArray) : State := bigEntryState input

theorem jump704 : Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 219 = true :=
  CycleSubmission.Global.Binding.jumpDest 146 (by rfl)

end CycleSubmission.Global.BigDispatch
