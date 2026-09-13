import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
set_option warningAsError true
set_option maxRecDepth 10000

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
  [opAt 463 .JUMPDEST, opAt 464 (.Dup ⟨2, by decide⟩),
   pushAt 465 1 96, opAt 466 .ADD]

def bigCheckModPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 467 (.Dup ⟨2, by decide⟩), opAt 468 (.Dup ⟨1, by decide⟩),
   opAt 469 .ADD]

def bigCheckComparePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 470 1 32, opAt 471 (.Dup ⟨3, by decide⟩), opAt 472 .GT]

def bigCheckJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 473 2 694, opAt 474 .JUMPI]

def bigCheckPath := bigCheckExpPath ++ bigCheckModPath ++
  bigCheckComparePath ++ bigCheckJumpPath

def bigTailFramePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 484 .JUMPDEST, pushAt 485 2 1194,
   opAt 486 (.Dup ⟨1, by decide⟩), opAt 487 (.Dup ⟨3, by decide⟩)]

def bigTailArgsPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 488 1 96, opAt 489 (.Dup ⟨6, by decide⟩),
   opAt 490 (.Dup ⟨8, by decide⟩), opAt 491 (.Dup ⟨10, by decide⟩)]

def bigTailJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 492 2 250, opAt 493 .JUMP]

def bigTailPath := bigTailFramePath ++ bigTailArgsPath ++ bigTailJumpPath

def bigExpOffsetState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 669
    stack := [UInt256.ofNat (96 + baseSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def bigOffsetsState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 672
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigComparedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 676
    stack := [1, UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigCheckedState (input : ByteArray) : State :=
  { Dispatch.wordCheckedState input with pc := UInt256.ofNat 694 }

def bigTailFrameState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 700
    stack := [UInt256.ofNat expOff, UInt256.ofNat modOff, UInt256.ofNat 1194,
      UInt256.ofNat modOff, UInt256.ofNat expOff, UInt256.ofNat m,
      UInt256.ofNat e, UInt256.ofNat b] }

def bigTailArgsState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 705
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1194, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

/-- Calling-convention state at the first instruction of `modexpBig`. -/
def bigEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 250
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1194, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

@[simp] theorem bigTailPCs (i : Nat)
    (hi : 484 ≤ i) (hii : i ≤ 493) :
    Artifact.submissionArtifact.instructionPC i =
      ([694,695,698,699,700,702,703,704,705,708] : List Nat)[i - 484]! := by
  interval_cases i <;> decide

theorem jump704 : Decode.isValidJumpDest submissionBytecode 250 = true :=
  Artifact.isValidJumpDest_index 175 (by rfl)

theorem jump1268 : Decode.isValidJumpDest submissionBytecode 694 = true :=
  Artifact.isValidJumpDest_index 484 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
