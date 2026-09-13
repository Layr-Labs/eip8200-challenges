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
  [opAt 900 .JUMPDEST, opAt 901 (.Dup ⟨2, by decide⟩),
   pushAt 902 1 96, opAt 903 .ADD]

def bigCheckModPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 904 (.Dup ⟨2, by decide⟩), opAt 905 (.Dup ⟨1, by decide⟩),
   opAt 906 .ADD]

def bigCheckComparePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 907 1 32, opAt 908 (.Dup ⟨3, by decide⟩), opAt 909 .GT]

def bigCheckJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 910 2 1236, opAt 911 .JUMPI]

def bigCheckPath := bigCheckExpPath ++ bigCheckModPath ++
  bigCheckComparePath ++ bigCheckJumpPath

def bigTailFramePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 921 .JUMPDEST, pushAt 922 2 1202,
   opAt 923 (.Dup ⟨1, by decide⟩), opAt 924 (.Dup ⟨3, by decide⟩)]

def bigTailArgsPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 925 1 96, opAt 926 (.Dup ⟨6, by decide⟩),
   opAt 927 (.Dup ⟨8, by decide⟩), opAt 928 (.Dup ⟨10, by decide⟩)]

def bigTailJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 929 2 719, opAt 930 .JUMP]

def bigTailPath := bigTailFramePath ++ bigTailArgsPath ++ bigTailJumpPath

def bigExpOffsetState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1211
    stack := [UInt256.ofNat (96 + baseSize input),
      UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
      UInt256.ofNat (baseSize input)] }

def bigOffsetsState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1214
    stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigComparedState (input : ByteArray) : State :=
  { Main.headerState input with
    pc := UInt256.ofNat 1218
    stack := [1, UInt256.ofNat (96 + (baseSize input + exponentSize input)),
      UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] }

def bigCheckedState (input : ByteArray) : State :=
  { Dispatch.wordCheckedState input with pc := UInt256.ofNat 1236 }

def bigTailFrameState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 1242
    stack := [UInt256.ofNat expOff, UInt256.ofNat modOff, UInt256.ofNat 1202,
      UInt256.ofNat modOff, UInt256.ofNat expOff, UInt256.ofNat m,
      UInt256.ofNat e, UInt256.ofNat b] }

def bigTailArgsState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 1247
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1202, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

/-- Calling-convention state at the first instruction of `modexpBig`. -/
def bigEntryState (input : ByteArray) : State :=
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := 96 + b
  let modOff := expOff + e
  { Main.headerState input with
    pc := UInt256.ofNat 719
    stack := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat 96, UInt256.ofNat expOff, UInt256.ofNat modOff,
      UInt256.ofNat 1202, UInt256.ofNat modOff, UInt256.ofNat expOff,
      UInt256.ofNat m, UInt256.ofNat e, UInt256.ofNat b] }

@[simp] theorem bigTailPCs (i : Nat)
    (hi : 921 ≤ i) (hii : i ≤ 930) :
    Artifact.submissionArtifact.instructionPC i =
      ([1236,1237,1240,1241,1242,1244,1245,1246,1247,1250] : List Nat)[i - 921]! := by
  interval_cases i <;> decide

theorem jump704 : Decode.isValidJumpDest submissionBytecode 719 = true :=
  Artifact.isValidJumpDest_index 560 (by rfl)

theorem jump1268 : Decode.isValidJumpDest submissionBytecode 1236 = true :=
  Artifact.isValidJumpDest_index 921 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
