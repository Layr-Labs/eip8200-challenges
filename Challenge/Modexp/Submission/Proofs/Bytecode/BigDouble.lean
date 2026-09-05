import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 300000

/-! # Specialized modular doubling

The appended dispatcher takes a conservative no-reduction shortcut when the
top limb proves that doubling stays below the modulus.  Otherwise its fused
loop doubles each limb and computes the subtraction candidate in one pass,
then selects the reduced or wrapped result with one `MCOPY`.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

/- Cache the appended fused suffix once.  Looking up every high global index
directly makes Lean repeatedly reduce the full 1349-instruction artifact. -/
private def fusedInstructionsLiteral : List Instr :=
 [Instr.op .JUMPDEST, Instr.push 1 1, Instr.op (.Dup ⟨5, by decide⟩),
  Instr.op .SUB, Instr.push 1 5, Instr.op .SHL,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.op (.Dup ⟨2, by decide⟩),
  Instr.op .ADD, Instr.op .MLOAD, Instr.op (.Dup ⟨0, by decide⟩),
  Instr.push 1 255, Instr.op .SHR, Instr.push 2 1618, Instr.op .JUMPI,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.op (.Dup ⟨0, by decide⟩),
  Instr.op .ADD, Instr.push 1 1, Instr.op .ADD,
  Instr.op (.Dup ⟨2, by decide⟩), Instr.op (.Dup ⟨7, by decide⟩),
  Instr.op .ADD, Instr.op .MLOAD, Instr.op (.Swap ⟨0, by decide⟩),
  Instr.op .LT, Instr.push 2 1625, Instr.op .JUMPI, Instr.op .JUMPDEST,
  Instr.op .POP, Instr.op .POP, Instr.push 2 1632, Instr.op .JUMP,
  Instr.op .JUMPDEST, Instr.op .POP, Instr.op .POP, Instr.push 2 1473,
  Instr.op .JUMP, Instr.op .JUMPDEST, Instr.op .POP,
  Instr.op (.Swap ⟨0, by decide⟩), Instr.op .POP, Instr.push 0 0,
  Instr.push 0 0, Instr.push 0 0, Instr.op .JUMPDEST,
  Instr.op (.Dup ⟨5, by decide⟩), Instr.op (.Dup ⟨1, by decide⟩),
  Instr.op .LT, Instr.op .ISZERO, Instr.push 2 1718, Instr.op .JUMPI,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.push 1 5, Instr.op .SHL,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.op (.Dup ⟨5, by decide⟩),
  Instr.op .ADD, Instr.op .MLOAD, Instr.op (.Dup ⟨4, by decide⟩),
  Instr.op (.Dup ⟨1, by decide⟩), Instr.op (.Dup ⟨2, by decide⟩),
  Instr.op .ADD, Instr.op .ADD, Instr.op (.Dup ⟨1, by decide⟩),
  Instr.push 1 255, Instr.op .SHR, Instr.op (.Swap ⟨5, by decide⟩),
  Instr.op .POP, Instr.op (.Dup ⟨0, by decide⟩),
  Instr.op (.Dup ⟨3, by decide⟩), Instr.op (.Dup ⟨8, by decide⟩),
  Instr.op .ADD, Instr.op .MSTORE, Instr.op (.Dup ⟨2, by decide⟩),
  Instr.op (.Dup ⟨8, by decide⟩), Instr.op .ADD, Instr.op .MLOAD,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.op (.Dup ⟨2, by decide⟩),
  Instr.op .SUB, Instr.op (.Dup ⟨6, by decide⟩),
  Instr.op (.Dup ⟨1, by decide⟩), Instr.op .SUB,
  Instr.op (.Dup ⟨2, by decide⟩), Instr.op (.Dup ⟨4, by decide⟩),
  Instr.op .LT, Instr.op (.Dup ⟨8, by decide⟩),
  Instr.op (.Dup ⟨3, by decide⟩), Instr.op .LT,
  Instr.op (.Dup ⟨2, by decide⟩), Instr.op (.Dup ⟨8, by decide⟩),
  Instr.push 2 5120, Instr.op .ADD, Instr.op .MSTORE,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.op (.Dup ⟨2, by decide⟩),
  Instr.op .OR, Instr.op (.Swap ⟨9, by decide⟩), Instr.op .POP,
  Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP,
  Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.push 1 1,
  Instr.op (.Dup ⟨1, by decide⟩), Instr.op .ADD,
  Instr.op (.Swap ⟨0, by decide⟩), Instr.op .POP, Instr.push 2 1639,
  Instr.op .JUMP, Instr.op .JUMPDEST, Instr.op .POP,
  Instr.op (.Dup ⟨0, by decide⟩), Instr.op .ISZERO,
  Instr.op (.Dup ⟨2, by decide⟩), Instr.op .OR, Instr.op .ISZERO,
  Instr.push 2 1738, Instr.op .JUMPI, Instr.op (.Dup ⟨4, by decide⟩),
  Instr.push 1 5, Instr.op .SHL, Instr.push 2 5120,
  Instr.op (.Dup ⟨4, by decide⟩), Instr.op .MCOPY, Instr.op .JUMPDEST,
  Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP,
  Instr.op .JUMP, Instr.op .JUMPDEST, Instr.op .POP, Instr.op .POP,
  Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP,
  Instr.op .POP, Instr.op .JUMP]

private def generalSkipInstructionsLiteral : List Instr :=
  [Instr.op .JUMPDEST, Instr.op (.Dup ⟨1, by decide⟩), Instr.op .ISZERO,
   Instr.push 2 1766, Instr.op .JUMPI, Instr.push 2 170, Instr.op .JUMP,
   Instr.op .JUMPDEST, Instr.push 1 1, Instr.op (.Dup ⟨8, by decide⟩),
   Instr.op .SUB, Instr.push 1 5, Instr.op .SHL,
   Instr.op (.Dup ⟨0, by decide⟩), Instr.op (.Dup ⟨5, by decide⟩),
   Instr.op .ADD, Instr.op .MLOAD, Instr.op (.Swap ⟨0, by decide⟩),
   Instr.op (.Dup ⟨8, by decide⟩), Instr.op .ADD, Instr.op .MLOAD,
   Instr.op (.Swap ⟨0, by decide⟩), Instr.op .LT, Instr.push 2 1792,
   Instr.op .JUMPI, Instr.push 2 170, Instr.op .JUMP,
   Instr.op .JUMPDEST, Instr.op .POP, Instr.op .POP, Instr.op .POP,
   Instr.op .POP, Instr.op .POP, Instr.op .POP, Instr.op .POP,
   Instr.op .POP, Instr.op .JUMP]

private def fusedInstructions : List Instr :=
  fusedInstructionsLiteral ++ generalSkipInstructionsLiteral

private theorem fusedInstructions_eq :
    Artifact.submissionInstructions.drop 1165 = fusedInstructions := by rfl

private def fusedLocatedAt (offset : Fin fusedInstructions.length) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka := by
  have hat : Artifact.submissionInstructions[1165 + offset.val]? =
      some fusedInstructions[offset.val] := by
    rw [← List.getElem?_drop, fusedInstructions_eq,
      List.getElem?_eq_getElem offset.isLt]
  exact
    { index := 1165 + offset.val
      instruction := fusedInstructions[offset.val]
      atIndex := by simpa [Artifact.submissionArtifact] using hat
      wellFormed := Artifact.allWellFormed.valid (List.mem_of_getElem? hat) }

private def fusedOpAt (offset : Nat) (op : Operation)
    (hgetTail : fusedInstructions[offset]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  have hat : Artifact.submissionInstructions[1165 + offset]? = some (.op op) := by
    rw [← List.getElem?_drop, fusedInstructions_eq]
    exact hgetTail
  ⟨1165 + offset, .op op, by simpa [Artifact.submissionArtifact] using hat,
    wfOp hopcode hplain havailable⟩

private def fusedPushAt (offset : Nat) (width : Fin 33) (value : UInt256)
    (hgetTail : fusedInstructions[offset]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  have hat : Artifact.submissionInstructions[1165 + offset]? =
      some (.push width value) := by
    rw [← List.getElem?_drop, fusedInstructions_eq]
    exact hgetTail
  ⟨1165 + offset, .push width value,
    by simpa [Artifact.submissionArtifact] using hat, hwf⟩

@[simp] private def locateSlice (start : Nat) (expected : List Instr)
    (hslice : (fusedInstructions.drop start).take expected.length = expected := by rfl) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  List.ofFn (n := expected.length) fun i => by
    have hsliceAt := congrArg (fun xs : List Instr => xs[i.val]?) hslice
    have hlocal : fusedInstructions[start + i.val]? = some expected[i.val] := by
      rw [← List.getElem?_drop]
      simpa [List.getElem?_take, i.isLt] using hsliceAt
    have hat : Artifact.submissionInstructions[1165 + (start + i.val)]? =
        some expected[i.val] := by
      rw [← List.getElem?_drop, fusedInstructions_eq]
      exact hlocal
    exact
      { index := 1165 + (start + i.val)
        instruction := expected[i.val]
        atIndex := by simpa [Artifact.submissionArtifact] using hat
        wellFormed := Artifact.allWellFormed.valid (List.mem_of_getElem? hat) }

@[simp] private def fusedBlock (start length : Nat)
    (hslice : (fusedInstructions.drop start).take length =
      (fusedInstructionsLiteral.drop start).take length := by rfl)
    (hlen : length ≤ fusedInstructionsLiteral.length - start := by decide) :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  locateSlice start ((fusedInstructionsLiteral.drop start).take length) (by
    simpa only [List.length_take, List.length_drop, Nat.min_eq_left hlen] using hslice)

def addSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1085 .JUMPDEST, opAt 1086 (.Dup ⟨2, by decide⟩), pushAt 1087 0 0,
   opAt 1088 .SUB, pushAt 1089 0 0, pushAt 1090 0 0]

def addGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1091 .JUMPDEST, opAt 1092 (.Dup ⟨7, by decide⟩),
   opAt 1093 (.Dup ⟨1, by decide⟩), opAt 1094 .EQ,
   pushAt 1095 2 1745, opAt 1096 .JUMPI]

def fastExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 137 10

def addBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1097 (.Dup ⟨0, by decide⟩), pushAt 1098 1 5, opAt 1099 .SHL,
   opAt 1100 (.Dup ⟨0, by decide⟩), opAt 1101 (.Dup ⟨5, by decide⟩),
   opAt 1102 .ADD, opAt 1103 .MLOAD,
   opAt 1104 (.Dup ⟨0, by decide⟩), pushAt 1105 1 255, opAt 1106 .SHR,
   opAt 1107 (.Swap ⟨0, by decide⟩), opAt 1108 (.Dup ⟨0, by decide⟩),
   opAt 1109 .ADD, opAt 1110 (.Dup ⟨4, by decide⟩), opAt 1111 .ADD,
   opAt 1112 (.Dup ⟨2, by decide⟩), opAt 1113 (.Dup ⟨7, by decide⟩),
   opAt 1114 .ADD, opAt 1115 .MSTORE,
   opAt 1116 (.Swap ⟨2, by decide⟩), opAt 1117 .POP, opAt 1118 .POP,
   pushAt 1119 1 1, opAt 1120 .ADD, pushAt 1121 2 1479, opAt 1122 .JUMP]

def dispatchCarryPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 0 15

def dispatchComparePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 15 13

def dispatchUnsafePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 28 5

def dispatchSafePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 33 5

def fusedSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 38 7

def fusedGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 45 7

def fusedBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 52 63

def fusedFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 115 9

def fusedCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 124 6

def fusedExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  fusedBlock 130 7


def entry (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1582
           stack := [dst, dst, 1, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

def topOffset (count : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat count - 1) (UInt256.ofNat 5)

def topLoaded (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) (pc : Nat) : State :=
  let off := topOffset count
  let addr := dst + off
  let x := MachineState.readWord s.memory addr.toNat
  { s with pc := UInt256.ofNat pc
           stack := [x, off, dst, dst, 1, modulus, UInt256.ofNat count,
             returnDest] ++ rest
           activeWords := UInt256.ofNat
             (MachineState.activeWordsAfter s.activeWords.toNat addr.toNat 32) }

def topCompared (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) (pc : Nat) : State :=
  let loaded := topLoaded s dst modulus count returnDest rest pc
  let off := topOffset count
  { loaded with
      pc := UInt256.ofNat pc
      activeWords := UInt256.ofNat (MachineState.activeWordsAfter
        loaded.activeWords.toNat (modulus + off).toNat 32) }

def topWord (s : State) (dst : UInt256) (count : Nat) : UInt256 :=
  MachineState.readWord s.memory (dst + topOffset count).toNat

def topCarry (s : State) (dst : UInt256) (count : Nat) : UInt256 :=
  UInt256.shiftRight (topWord s dst count) (UInt256.ofNat 255)

def topSum (s : State) (dst : UInt256) (count : Nat) : UInt256 :=
  (topWord s dst count + topWord s dst count) + 1

def modulusTop (s : State) (modulus : UInt256) (count : Nat) : UInt256 :=
  MachineState.readWord s.memory (modulus + topOffset count).toNat

def safeTop (s : State) (dst modulus : UInt256) (count : Nat) : Prop :=
  (topCarry s dst count).toNat = 0 ∧
    (topSum s dst count).toNat < (modulusTop s modulus count).toNat

def fusedEntry (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1632
           stack := [dst, dst, 1, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

structure FusedProgress where
  memory : ByteArray
  activeWords : UInt256
  carry : UInt256
  borrow : UInt256

def fusedProgress (memory : ByteArray) (activeWords dst modulus : UInt256) :
    Nat → FusedProgress
  | 0 => ⟨memory, activeWords, 0, 0⟩
  | i + 1 =>
      let before := fusedProgress memory activeWords dst modulus i
      let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
      let dstAt := dst + off
      let modulusAt := modulus + off
      let candidateAt := UInt256.ofNat 5120 + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let z := (x + x) + before.carry
      let carry := UInt256.shiftRight x (UInt256.ofNat 255)
      let loadedDst := UInt256.ofNat (MachineState.activeWordsAfter
        before.activeWords.toNat dstAt.toNat 32)
      let storedDst := MachineState.writeBytes before.memory
        (Data.Bytes.natToBytesPadded z.toNat 32) dstAt.toNat
      let y := MachineState.readWord storedDst modulusAt.toNat
      let loadedModulus := UInt256.ofNat (MachineState.activeWordsAfter
        loadedDst.toNat modulusAt.toNat 32)
      let difference := z - y
      let candidate := difference - before.borrow
      let borrow := UInt256.lor (UInt256.lt z y)
        (UInt256.lt difference before.borrow)
      let stored := UInt256.ofNat (MachineState.activeWordsAfter
        loadedModulus.toNat candidateAt.toNat 32)
      ⟨MachineState.writeBytes storedDst
          (Data.Bytes.natToBytesPadded candidate.toNat 32) candidateAt.toNat,
        stored, carry, borrow⟩

def fusedLoop (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := fusedProgress s.memory s.activeWords dst modulus i
  { s with pc := UInt256.ofNat 1639
           stack := [UInt256.ofNat i, progress.borrow, progress.carry,
             dst, modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def fusedBodyEntry (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { fusedLoop s dst modulus count i returnDest rest with pc := UInt256.ofNat 1648 }

def fusedAtFinish (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) (pc : Nat) : State :=
  let progress := fusedProgress s.memory s.activeWords dst modulus count
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat count, progress.borrow, progress.carry, dst, modulus,
             UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def fusedChoice (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) (pc : Nat) : State :=
  let progress := fusedProgress s.memory s.activeWords dst modulus count
  { s with pc := UInt256.ofNat pc
           stack := [progress.borrow, progress.carry, dst, modulus,
             UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def fusedUseSub (s : State) (dst modulus : UInt256) (count : Nat) : UInt256 :=
  let progress := fusedProgress s.memory s.activeWords dst modulus count
  UInt256.lor progress.carry (UInt256.isZero progress.borrow)

def fusedCopied (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let before := fusedChoice s dst modulus count returnDest rest 1729
  let size := BigHelpers.mcopySize count
  { before with
      pc := UInt256.ofNat 1738
      memory := MachineState.writeBytes before.memory
        (MachineState.readPadded before.memory 5120 size.toNat) dst.toNat
      activeWords := UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter before.activeWords.toNat dst.toNat size.toNat)
        5120 size.toNat) }

def fusedReturned (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let useSub := fusedUseSub s dst modulus count
  let progress := fusedProgress s.memory s.activeWords dst modulus count
  let selected := BigHelpers.maskChoice progress.memory progress.activeWords dst
    (0 - useSub) count
  { s with pc := returnDest
           stack := rest
           memory := selected.memory
           activeWords := selected.activeWords }

def addOnlyReturned (s : State) (dst _modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let progress := BigHelpers.addProgress s.memory s.activeWords dst dst (0 - 1) count
  { s with pc := returnDest
           stack := rest
           memory := progress.memory
           activeWords := progress.activeWords }

def returned (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  if (topCarry s dst count).toNat = 0 then
    if (topSum s dst count).toNat < (modulusTop s modulus count).toNat then
      addOnlyReturned
        (topCompared s dst modulus count returnDest rest 1625)
        dst modulus count returnDest rest
    else
      fusedReturned
        (topCompared s dst modulus count returnDest rest 1618)
        dst modulus count returnDest rest
  else
    fusedReturned
      (topLoaded s dst modulus count returnDest rest 1618)
      dst modulus count returnDest rest


/- Correctness and preservation lemmas are split into `BigDoubleCorrect` while
the exact bytecode execution proof is iterated on below. -/
/-
theorem readWord_fusedProgress_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter j : Nat)
    (hiter : iter ≤ count) (hj : j < count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr) :
    MachineState.readWord
        (fusedProgress memory activeWords (UInt256.ofNat dst) modulus iter).memory
        (ptr + 32 * j) =
      MachineState.readWord memory (ptr + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      simp only [fusedProgress]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega)
        · have hsize (value : Nat) :
              (Data.Bytes.natToBytesPadded value 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, BigHelpers.addOffset_toNat dst iter (by omega)]
          rcases hptrDst with hbefore | hafter
          · left; omega
          · right; omega
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, BigHelpers.addOffset_toNat 5120 iter (by omega)]
        rcases hptrCandidate with hbefore | hafter
        · right; omega
        · left; omega

theorem represents_fusedProgress_disjoint_region (memory : ByteArray)
    (activeWords modulus : UInt256) (dst ptr count iter value : Nat)
    (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents memory ptr count value) :
    Limbs.Represents
      (fusedProgress memory activeWords (UInt256.ofNat dst) modulus iter).memory
      ptr count value := by
  refine ⟨hrep.1, ?_⟩
  unfold Limbs.memoryLimbs
  rw [← hrep.2]
  apply List.map_congr_left
  intro j hj
  rw [readWord_fusedProgress_disjoint_region memory activeWords modulus dst ptr
    count iter j hiter (by simpa using hj) hdstFit hcandidateFit hptrDst
    hptrCandidate]

theorem readWord_fusedProgress_future_dst (memory : ByteArray)
    (activeWords modulus : UInt256) (dst count iter j : Nat)
    (hiter : iter ≤ j) (hj : j < count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst) :
    MachineState.readWord
        (fusedProgress memory activeWords (UInt256.ofNat dst) modulus iter).memory
        (dst + 32 * j) = MachineState.readWord memory (dst + 32 * j) := by
  induction iter with
  | zero => rfl
  | succ iter ih =>
      simp only [fusedProgress]
      rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
      · rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · exact ih (by omega)
        · have hsize (value : Nat) :
              (Data.Bytes.natToBytesPadded value 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, BigHelpers.addOffset_toNat dst iter (by omega)]
          right; omega
      · have hsize (value : Nat) :
            (Data.Bytes.natToBytesPadded value 32).size = 32 := by
          simp [Data.Bytes.natToBytesPadded, ByteArray.size]
        rw [hsize, BigHelpers.addOffset_toNat 5120 iter (by omega)]
        rcases hdstCandidate with hbefore | hafter
        · left; omega
        · right; omega

private theorem memoryLimbs_writeWord_disjoint (memory : ByteArray)
    (writeAt ptr count : Nat) (value : UInt256)
    (hdisjoint : writeAt + 32 ≤ ptr ∨ ptr + 32 * count ≤ writeAt) :
    Limbs.memoryLimbs
      (MachineState.writeBytes memory (Data.Bytes.natToBytesPadded value.toNat 32)
        writeAt) ptr count = Limbs.memoryLimbs memory ptr count := by
  unfold Limbs.memoryLimbs
  apply List.map_congr_left
  intro j hj
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  have hjlt : j < count := by simpa using hj
  have hsize : (Data.Bytes.natToBytesPadded value.toNat 32).size = 32 := by
    simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  rw [hsize]
  rcases hdisjoint with hbefore | hafter
  · left; omega
  · right; omega

structure FusedNatProgress where
  digits : List Nat
  candidates : List Nat
  carry : Nat
  borrow : Nat

def fusedNatProgress (memory : ByteArray) (dst modulus : Nat) :
    Nat → FusedNatProgress
  | 0 => ⟨[], [], 0, 0⟩
  | i + 1 =>
      let before := fusedNatProgress memory dst modulus i
      let x := (MachineState.readWord memory (dst + 32 * i)).toNat
      let y := (MachineState.readWord memory (modulus + 32 * i)).toNat
      let total := x + x + before.carry
      let z := total % Limbs.radix
      let carry := total / Limbs.radix
      let nextBorrow := if z < y + before.borrow then 1 else 0
      let candidate := z + Limbs.radix * nextBorrow - y - before.borrow
      ⟨before.digits ++ [z], before.candidates ++ [candidate], carry,
        nextBorrow⟩

theorem fusedNatProgress_canonical (memory : ByteArray)
    (dst modulus count : Nat) :
    let natural := fusedNatProgress memory dst modulus count
    let added := Limbs.addDigitLists
      (Limbs.memoryLimbs memory dst count)
      (Limbs.memoryLimbs memory dst count) 0
    let subtracted := Limbs.subDigitLists natural.digits
      (Limbs.memoryLimbs memory modulus count) 0
    natural.digits = added.1 ∧ natural.carry = added.2 ∧
      natural.candidates = subtracted.1 ∧ natural.borrow = subtracted.2 := by
  induction count with
  | zero =>
      simp [fusedNatProgress, Limbs.memoryLimbs, Limbs.addDigitLists,
        Limbs.subDigitLists]
  | succ count ih =>
      rw [fusedNatProgress, BigHelpers.memoryLimbs_succ,
        BigHelpers.memoryLimbs_succ,
        Limbs.addDigitLists_append_single (by simp [Limbs.memoryLimbs])]
      rcases ih with ⟨hdigits, hcarry, hcandidates, hborrow⟩
      simp only
      rw [hdigits, hcarry]
      rw [Limbs.subDigitLists_append_single (by simp), hcandidates, hborrow]
      exact ⟨rfl, rfl, rfl, rfl⟩

theorem fusedProgress_matches_nat (memory : ByteArray) (activeWords : UInt256)
    (dst modulus count iter : Nat) (hiter : iter ≤ count)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hmodulusFit : modulus + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hdstModulus : dst + 32 * count ≤ modulus ∨
      modulus + 32 * count ≤ dst)
    (hdstCandidate : dst + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ dst)
    (hmodulusCandidate : modulus + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ modulus) :
    let progress := fusedProgress memory activeWords (UInt256.ofNat dst)
      (UInt256.ofNat modulus) iter
    let natural := fusedNatProgress memory dst modulus iter
    Limbs.memoryLimbs progress.memory dst iter = natural.digits ∧
      Limbs.memoryLimbs progress.memory 5120 iter = natural.candidates ∧
      progress.carry.toNat = natural.carry ∧
      progress.borrow.toNat = natural.borrow ∧
      natural.carry ≤ 1 ∧ natural.borrow ≤ 1 := by
  induction iter with
  | zero =>
      have hzero : (0 : UInt256).toNat = 0 := by decide
      simp [fusedProgress, fusedNatProgress, Limbs.memoryLimbs, hzero]
  | succ iter ih =>
      have hi : iter < count := by omega
      have hprefix := ih (by omega)
      let before := fusedProgress memory activeWords (UInt256.ofNat dst)
        (UInt256.ofNat modulus) iter
      let naturalBefore := fusedNatProgress memory dst modulus iter
      have hbeforeDst :
          Limbs.memoryLimbs before.memory dst iter = naturalBefore.digits :=
        hprefix.1
      have hbeforeCandidate :
          Limbs.memoryLimbs before.memory 5120 iter = naturalBefore.candidates :=
        hprefix.2.1
      have hbeforeCarry : before.carry.toNat = naturalBefore.carry :=
        hprefix.2.2.1
      have hbeforeBorrow : before.borrow.toNat = naturalBefore.borrow :=
        hprefix.2.2.2.1
      have hcarryLe : naturalBefore.carry ≤ 1 := hprefix.2.2.2.2.1
      have hborrowLe : naturalBefore.borrow ≤ 1 := hprefix.2.2.2.2.2
      let off := UInt256.shiftLeft (UInt256.ofNat iter) (UInt256.ofNat 5)
      let dstAt := UInt256.ofNat dst + off
      let modulusAt := UInt256.ofNat modulus + off
      let candidateAt := UInt256.ofNat 5120 + off
      let x := MachineState.readWord before.memory dstAt.toNat
      let z := (x + x) + before.carry
      let storedDst := MachineState.writeBytes before.memory
        (Data.Bytes.natToBytesPadded z.toNat 32) dstAt.toNat
      let y := MachineState.readWord storedDst modulusAt.toNat
      let difference := z - y
      let candidate := difference - before.borrow
      have hoffDst : dstAt.toNat = dst + 32 * iter := by
        exact BigHelpers.addOffset_toNat dst iter (by omega)
      have hoffModulus : modulusAt.toNat = modulus + 32 * iter := by
        exact BigHelpers.addOffset_toNat modulus iter (by omega)
      have hoffCandidate : candidateAt.toNat = 5120 + 32 * iter := by
        exact BigHelpers.addOffset_toNat 5120 iter (by omega)
      have hx : x = MachineState.readWord memory (dst + 32 * iter) := by
        simpa [x, dstAt, hoffDst, before] using
          readWord_fusedProgress_future_dst memory activeWords
            (UInt256.ofNat modulus) dst count iter iter (by omega) hi
            hdstFit hcandidateFit hdstCandidate
      have hyBefore : MachineState.readWord before.memory (modulus + 32 * iter) =
          MachineState.readWord memory (modulus + 32 * iter) := by
        exact readWord_fusedProgress_disjoint_region memory activeWords
          (UInt256.ofNat modulus) dst modulus count iter iter (by omega) hi
          hdstFit hcandidateFit hdstModulus hmodulusCandidate
      have hy : y = MachineState.readWord memory (modulus + 32 * iter) := by
        rw [y, Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
        · simpa [modulusAt, hoffModulus, before] using hyBefore
        · have hsize : (Data.Bytes.natToBytesPadded z.toNat 32).size = 32 := by
            simp [Data.Bytes.natToBytesPadded, ByteArray.size]
          rw [hsize, hoffDst, hoffModulus]
          rcases hdstModulus with hbefore | hafter
          · left; omega
          · right; omega
      have hadd := BigHelpers.addLimbStep_toNat x x before.carry
        (by simpa [hbeforeCarry] using hcarryLe)
      have hcarryEq := doubleCarry_eq x before.carry
        (by simpa [hbeforeCarry] using hcarryLe)
      have hsub := BigHelpers.subLimbStep_toNat z y before.borrow
        (by simpa [hbeforeBorrow] using hborrowLe)
      have hdstMemory :
          Limbs.memoryLimbs
            (fusedProgress memory activeWords (UInt256.ofNat dst)
              (UInt256.ofNat modulus) (iter + 1)).memory dst (iter + 1) =
            naturalBefore.digits ++ [z.toNat] := by
        simp only [fusedProgress]
        rw [memoryLimbs_writeWord_disjoint]
        · rw [hoffDst, BigHelpers.memoryLimbs_write_next, hbeforeDst]
        · rw [hoffCandidate]
          rcases hdstCandidate with hbefore | hafter
          · right; omega
          · left; omega
      have hcandidateMemory :
          Limbs.memoryLimbs
            (fusedProgress memory activeWords (UInt256.ofNat dst)
              (UInt256.ofNat modulus) (iter + 1)).memory 5120 (iter + 1) =
            naturalBefore.candidates ++ [candidate.toNat] := by
        simp only [fusedProgress]
        rw [hoffCandidate, BigHelpers.memoryLimbs_write_next]
        rw [memoryLimbs_writeWord_disjoint, hbeforeCandidate]
        rw [hoffDst]
        rcases hdstCandidate with hbefore | hafter
        · left; omega
        · right; omega
      dsimp only [fusedNatProgress]
      rw [hdstMemory, hcandidateMemory]
      constructor
      · congr 2
        simpa [z, hx, hbeforeCarry, naturalBefore] using hadd.1
      · constructor
        · congr 2
          simpa [candidate, difference, z, y, hx, hy, hbeforeBorrow,
            hbeforeCarry, naturalBefore] using hsub.1
        · constructor
          · simpa [hcarryEq, hx, hbeforeCarry, naturalBefore] using hadd.2
          · constructor
            · simpa [candidate, difference, z, y, hx, hy, hbeforeBorrow,
                hbeforeCarry, naturalBefore] using hsub.2
            · constructor
              · have hxLt := x.val.isLt
                have htotal : x.toNat + x.toNat + before.carry.toNat <
                    2 * Limbs.radix := by
                  simp only [Limbs.radix]
                  omega
                have hdiv : (x.toNat + x.toNat + before.carry.toNat) /
                    Limbs.radix < 2 := by
                  exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using htotal)
                simpa [hx, hbeforeCarry, naturalBefore] using Nat.le_of_lt_succ hdiv
              · by_cases hz : z.toNat < y.toNat + before.borrow.toNat
                · simp [hz]
                · simp [hz]

theorem fusedReturned_preserves_region (s : State)
    (dst modulus ptr count value : Nat) (returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (fusedReturned s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest).memory ptr count value := by
  let progress := fusedProgress s.memory s.activeWords (UInt256.ofNat dst)
    (UInt256.ofNat modulus) count
  have hprogress : Limbs.Represents progress.memory ptr count value := by
    exact represents_fusedProgress_disjoint_region s.memory s.activeWords
      (UInt256.ofNat modulus) dst ptr count count value (by omega) hdstFit
      hcandidateFit hptrDst hptrCandidate hrep
  let useSub := fusedUseSub s (UInt256.ofNat dst) (UInt256.ofNat modulus) count
  by_cases hmask : (0 - useSub).toNat = 0
  · have hgoal : Limbs.Represents
        (BigHelpers.maskChoice progress.memory progress.activeWords
          (UInt256.ofNat dst) (0 - useSub) count).memory ptr count value := by
      rw [BigHelpers.maskChoice_of_zero _ _ _ _ _ hmask]
      exact hprogress
    simpa [fusedReturned, fusedUseSub, progress, useSub] using hgoal

  · have hdstNat : (UInt256.ofNat dst).toNat = dst := by
      rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hsize : (BigHelpers.mcopySize count).toNat = 32 * count :=
      BigHelpers.mcopySize_toNat count (by omega)
    have hcopy := Mcopy.represents_mcopy_disjoint_region progress.memory
      dst 5120 count ptr count value
      (by rcases hptrDst with h | h
          · exact Or.inr h
          · exact Or.inl h)
      hprogress
    have hgoal : Limbs.Represents
        (BigHelpers.maskChoice progress.memory progress.activeWords
          (UInt256.ofNat dst) (0 - useSub) count).memory ptr count value := by
      rw [BigHelpers.maskChoice_of_pos _ _ _ _ _ hmask]
      simpa [hsize, hdstNat] using hcopy
    simpa [fusedReturned, fusedUseSub, progress, useSub] using hgoal

theorem returned_preserves_region (s : State)
    (dst modulus ptr count value : Nat) (returnDest : UInt256)
    (rest : List UInt256)
    (hdstFit : dst + 32 * count < 2 ^ 256)
    (hcandidateFit : 5120 + 32 * count < 2 ^ 256)
    (hptrDst : dst + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ dst)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨
      5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (returned s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest).memory ptr count value := by
  by_cases hcarry : (topCarry s (UInt256.ofNat dst) count).toNat = 0
  · by_cases hsafe :
        (topSum s (UInt256.ofNat dst) count).toNat <
          (modulusTop s (UInt256.ofNat modulus) count).toNat
    · have hadd := BigHelpers.represents_addProgress_disjoint_region
        s.memory
        (topCompared s (UInt256.ofNat dst) (UInt256.ofNat modulus)
          count returnDest rest 1625).activeWords
        (UInt256.ofNat dst) (0 - 1) dst ptr count count value
        (by omega) hdstFit hptrDst hrep
      simpa [returned, hcarry, hsafe, addOnlyReturned, topCompared, topLoaded]
        using hadd
    · have hfused := fusedReturned_preserves_region
        (topCompared s (UInt256.ofNat dst) (UInt256.ofNat modulus)
          count returnDest rest 1618)
        dst modulus ptr count value returnDest rest hdstFit hcandidateFit
        hptrDst hptrCandidate (by simpa [topCompared, topLoaded] using hrep)
      simpa [returned, hcarry, hsafe] using hfused
  · have hfused := fusedReturned_preserves_region
      (topLoaded s (UInt256.ofNat dst) (UInt256.ofNat modulus)
        count returnDest rest 1618)
      dst modulus ptr count value returnDest rest hdstFit hcandidateFit
      hptrDst hptrCandidate (by simpa [topLoaded] using hrep)
    simpa [returned, hcarry] using hfused

-/

def addEntry (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1473
           stack := [dst, dst, 1, modulus, UInt256.ofNat count,
             returnDest] ++ rest }

def loop (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let mask : UInt256 := 0 - 1
  let progress := BigHelpers.addProgress s.memory s.activeWords dst dst mask i
  { s with pc := UInt256.ofNat 1479
           stack := [UInt256.ofNat i, progress.carry, mask, dst, dst, 1,
             modulus, UInt256.ofNat count, returnDest] ++ rest
           memory := progress.memory
           activeWords := progress.activeWords }

def bodyEntry (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { loop s dst modulus count i returnDest rest with pc := UInt256.ofNat 1487 }

/- The full legacy table is replaced below by block-local cached PC tables. -/
/-
set_option maxHeartbeats 3000000 in
@[simp] private theorem doublePCs (i : Nat) (hi : 1085 ≤ i) (hii : i ≤ 1122) :
    Artifact.submissionArtifact.instructionPC i =
      [1473,1474,1475,1476,1477,1478,1479,1480,1481,1482,1483,1486,
       1487,1488,1490,1491,1492,1493,1494,1495,1496,1498,1499,1500,
       1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1513,
       1514,1517][i - 1085]! := by
  interval_cases i <;> decide
-/

@[simp] private theorem addSetupPCs (i : Nat) (hi : 1085 ≤ i)
    (hii : i ≤ 1090) :
    Artifact.submissionArtifact.instructionPC i =
      [1473,1474,1475,1476,1477,1478][i - 1085]! := by
  interval_cases i <;> decide

@[simp] private theorem addGuardPCs (i : Nat) (hi : 1091 ≤ i)
    (hii : i ≤ 1096) :
    Artifact.submissionArtifact.instructionPC i =
      [1479,1480,1481,1482,1483,1486][i - 1091]! := by
  interval_cases i <;> decide

@[simp] private theorem addBodyPCs (i : Nat) (hi : 1097 ≤ i)
    (hii : i ≤ 1122) :
    Artifact.submissionArtifact.instructionPC i =
      [1487,1488,1490,1491,1492,1493,1494,1495,1496,1498,1499,1500,
       1501,1502,1503,1504,1505,1506,1507,1508,1509,1510,1511,1513,
       1514,1517][i - 1097]! := by
  interval_cases i <;> decide

private theorem jump1479 :
    Decode.isValidJumpDest submissionBytecode 1479 = true :=
  Artifact.isValidJumpDest_index 1091 (by rfl)

private theorem jump1473 :
    Decode.isValidJumpDest submissionBytecode 1473 = true :=
  Artifact.isValidJumpDest_index 1085 (by rfl)

private theorem jump1745 :
    Decode.isValidJumpDest submissionBytecode 1745 = true :=
  Artifact.isValidJumpDest_index 1302 (by rfl)

/-
set_option maxHeartbeats 3000000 in
@[simp] private theorem fusedPCs (i : Nat) (hi : 1165 ≤ i) (hii : i ≤ 1311) :
    Artifact.submissionArtifact.instructionPC i =
      [1582,1583,1585,1586,1587,1589,1590,1591,1592,1593,1594,1595,
       1597,1598,1601,1602,1603,1604,1605,1607,1608,1609,1610,1611,
       1612,1613,1614,1617,1618,1619,1620,1621,1624,1625,1626,1627,
       1628,1631,1632,1633,1634,1635,1636,1637,1638,1639,1640,1641,
       1642,1643,1644,1647,1648,1649,1651,1652,1653,1654,1655,1656,
       1657,1658,1659,1660,1661,1662,1664,1665,1666,1667,1668,1669,
       1670,1671,1672,1673,1674,1675,1676,1677,1678,1679,1680,1681,
       1682,1683,1684,1685,1686,1687,1688,1689,1690,1693,1694,1695,
       1696,1697,1698,1699,1700,1701,1702,1703,1704,1705,1706,1707,
       1708,1710,1711,1712,1713,1714,1717,1718,1719,1720,1721,1722,
       1723,1724,1725,1728,1729,1730,1732,1733,1736,1737,1738,1739,
       1740,1741,1742,1743,1744,1745,1746,1747,1748,1749,1750,1751,
       1752,1753,1754][i - 1165]! := by
  interval_cases i <;> decide
-/

@[simp] private theorem dispatchCarryPCs (i : Nat) (hi : 1165 ≤ i)
    (hii : i ≤ 1179) :
    Artifact.submissionArtifact.instructionPC i =
      [1582,1583,1585,1586,1587,1589,1590,1591,1592,1593,1594,1595,
       1597,1598,1601][i - 1165]! := by
  interval_cases i <;> decide

@[simp] private theorem dispatchComparePCs (i : Nat) (hi : 1180 ≤ i)
    (hii : i ≤ 1192) :
    Artifact.submissionArtifact.instructionPC i =
      [1602,1603,1604,1605,1607,1608,1609,1610,1611,1612,1613,1614,
       1617][i - 1180]! := by
  interval_cases i <;> decide

@[simp] private theorem dispatchUnsafePCs (i : Nat) (hi : 1193 ≤ i)
    (hii : i ≤ 1197) :
    Artifact.submissionArtifact.instructionPC i =
      [1618,1619,1620,1621,1624][i - 1193]! := by
  interval_cases i <;> decide

@[simp] private theorem dispatchSafePCs (i : Nat) (hi : 1198 ≤ i)
    (hii : i ≤ 1202) :
    Artifact.submissionArtifact.instructionPC i =
      [1625,1626,1627,1628,1631][i - 1198]! := by
  interval_cases i <;> decide

@[simp] private theorem fusedSetupPCs (i : Nat) (hi : 1203 ≤ i)
    (hii : i ≤ 1209) :
    Artifact.submissionArtifact.instructionPC i =
      [1632,1633,1634,1635,1636,1637,1638][i - 1203]! := by
  interval_cases i <;> decide

@[simp] private theorem fusedGuardPCs (i : Nat) (hi : 1210 ≤ i)
    (hii : i ≤ 1216) :
    Artifact.submissionArtifact.instructionPC i =
      [1639,1640,1641,1642,1643,1644,1647][i - 1210]! := by
  interval_cases i <;> decide

set_option maxHeartbeats 1000000 in
@[simp] private theorem fusedBodyPCs (i : Nat) (hi : 1217 ≤ i)
    (hii : i ≤ 1279) :
    Artifact.submissionArtifact.instructionPC i =
      [1648,1649,1651,1652,1653,1654,1655,1656,1657,1658,1659,1660,
       1661,1662,1664,1665,1666,1667,1668,1669,1670,1671,1672,1673,
       1674,1675,1676,1677,1678,1679,1680,1681,1682,1683,1684,1685,
       1686,1687,1688,1689,1690,1693,1694,1695,1696,1697,1698,1699,
       1700,1701,1702,1703,1704,1705,1706,1707,1708,1710,1711,1712,
       1713,1714,1717][i - 1217]! := by
  interval_cases i <;> decide

@[simp] private theorem fusedFinishPCs (i : Nat) (hi : 1280 ≤ i)
    (hii : i ≤ 1288) :
    Artifact.submissionArtifact.instructionPC i =
      [1718,1719,1720,1721,1722,1723,1724,1725,1728][i - 1280]! := by
  interval_cases i <;> decide

@[simp] private theorem fusedCopyPCs (i : Nat) (hi : 1289 ≤ i)
    (hii : i ≤ 1294) :
    Artifact.submissionArtifact.instructionPC i =
      [1729,1730,1732,1733,1736,1737][i - 1289]! := by
  interval_cases i <;> decide

@[simp] private theorem fusedExitPCs (i : Nat) (hi : 1295 ≤ i)
    (hii : i ≤ 1301) :
    Artifact.submissionArtifact.instructionPC i =
      [1738,1739,1740,1741,1742,1743,1744][i - 1295]! := by
  interval_cases i <;> decide

@[simp] private theorem fastExitPCs (i : Nat) (hi : 1302 ≤ i)
    (hii : i ≤ 1311) :
    Artifact.submissionArtifact.instructionPC i =
      [1745,1746,1747,1748,1749,1750,1751,1752,1753,1754][i - 1302]! := by
  interval_cases i <;> decide

private theorem jump1618 :
    Decode.isValidJumpDest submissionBytecode 1618 = true :=
  Artifact.isValidJumpDest_index 1193 (by rfl)

private theorem jump1625 :
    Decode.isValidJumpDest submissionBytecode 1625 = true :=
  Artifact.isValidJumpDest_index 1198 (by rfl)

private theorem jump1632 :
    Decode.isValidJumpDest submissionBytecode 1632 = true :=
  Artifact.isValidJumpDest_index 1203 (by rfl)

private theorem jump1639 :
    Decode.isValidJumpDest submissionBytecode 1639 = true :=
  Artifact.isValidJumpDest_index 1210 (by rfl)

private theorem jump1718 :
    Decode.isValidJumpDest submissionBytecode 1718 = true :=
  Artifact.isValidJumpDest_index 1280 (by rfl)

private theorem jump1738 :
    Decode.isValidJumpDest submissionBytecode 1738 = true :=
  Artifact.isValidJumpDest_index 1295 (by rfl)


private theorem fusedProgress_carry_le_one (memory : ByteArray)
    (activeWords dst modulus : UInt256) (i : Nat) :
    (fusedProgress memory activeWords dst modulus i).carry.toNat ≤ 1 := by
  cases i with
  | zero =>
      simp only [fusedProgress]
      decide
  | succ i =>
      simp only [fusedProgress]
      rw [Challenge.EvmProof.Word.shiftRight_toNat _ (by omega)]
      rw [Nat.shiftRight_eq_div_pow]
      have hx : (MachineState.readWord
          (fusedProgress memory activeWords dst modulus i).memory
          ((dst.toNat + (UInt256.shiftLeft (UInt256.ofNat i)
            (UInt256.ofNat 5)).toNat) % (2 ^ 256))).toNat < 2 ^ 256 := by
        exact (MachineState.readWord
          (fusedProgress memory activeWords dst modulus i).memory
          ((dst.toNat + (UInt256.shiftLeft (UInt256.ofNat i)
            (UInt256.ofNat 5)).toNat) % (2 ^ 256))).val.isLt
      norm_num at hx ⊢
      apply (Nat.div_le_iff_le_mul (by norm_num)).2
      omega

private theorem fusedProgress_borrow_le_one (memory : ByteArray)
    (activeWords dst modulus : UInt256) (i : Nat) :
    (fusedProgress memory activeWords dst modulus i).borrow.toNat ≤ 1 := by
  cases i with
  | zero =>
      simp only [fusedProgress]
      decide
  | succ i =>
      simp only [fusedProgress]
      simp only [Challenge.EvmProof.Word.word_toNat_lor,
        Challenge.EvmProof.Word.word_toNat_lt]
      split <;> split <;> norm_num

set_option linter.unusedSimpArgs false in
private theorem activeWordsAfter32_lt (active offset : UInt256) :
    MachineState.activeWordsAfter active.toNat offset.toNat 32 < 2 ^ 256 := by
  unfold MachineState.activeWordsAfter
  simp only [if_false]
  apply (Nat.max_lt).2
  constructor
  · exact active.val.isLt
  · have hoff : offset.toNat < 2 ^ 256 := offset.val.isLt
    have hdiv : (offset.toNat + 32 - 1) / 32 < 2 ^ 256 := by
      apply Nat.div_lt_of_lt_mul
      omega
    omega

@[simp] private theorem activeWordsAfter32_word_toNat (active offset : UInt256) :
    (UInt256.ofNat
      (MachineState.activeWordsAfter active.toNat offset.toNat 32)).toNat =
        MachineState.activeWordsAfter active.toNat offset.toNat 32 := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (activeWordsAfter32_lt active offset)]

private theorem activeWordsAfter32_idem (active offset : Nat) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active offset 32) offset 32 =
      MachineState.activeWordsAfter active offset 32 := by
  simp [MachineState.activeWordsAfter]

@[simp] private theorem activeWordsAfter32_mod_idem (active offset : UInt256) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active.toNat offset.toNat 32 % 2 ^ 256)
        offset.toNat 32 % 2 ^ 256 =
      MachineState.activeWordsAfter active.toNat offset.toNat 32 % 2 ^ 256 := by
  have hlt := activeWordsAfter32_lt active offset
  simp only [Nat.mod_eq_of_lt hlt, activeWordsAfter32_idem]

private theorem activeWordsAfter32_mod_idem_nat (active offset : Nat)
    (hactive : active < 2 ^ 256) (hoffset : offset < 2 ^ 256) :
    MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active offset 32 % 2 ^ 256)
        offset 32 % 2 ^ 256 =
      MachineState.activeWordsAfter active offset 32 % 2 ^ 256 := by
  have hlt := activeWordsAfter32_lt (UInt256.ofNat active) (UInt256.ofNat offset)
  simp only [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hactive, Nat.mod_eq_of_lt hoffset] at hlt
  rw [Nat.mod_eq_of_lt hlt, activeWordsAfter32_idem, Nat.mod_eq_of_lt hlt]

@[simp] private theorem activeWordsAfter32_word_idem
    (active offset : UInt256) :
    UInt256.ofNat (MachineState.activeWordsAfter
        (UInt256.ofNat
          (MachineState.activeWordsAfter active.toNat offset.toNat 32)).toNat
        offset.toNat 32) =
      UInt256.ofNat
        (MachineState.activeWordsAfter active.toNat offset.toNat 32) := by
  rw [activeWordsAfter32_word_toNat, activeWordsAfter32_idem]

@[simp] private theorem activeWordsAfter32_word_twice_eq_thrice
    (active offset : UInt256) :
    UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter active.toNat offset.toNat 32 % 2 ^ 256)
        offset.toNat 32) =
      UInt256.ofNat (MachineState.activeWordsAfter
        (MachineState.activeWordsAfter
          (MachineState.activeWordsAfter active.toNat offset.toNat 32 % 2 ^ 256)
          offset.toNat 32 % 2 ^ 256)
        offset.toNat 32) := by
  have hlt := activeWordsAfter32_lt active offset
  simp only [Nat.mod_eq_of_lt hlt, activeWordsAfter32_idem]

set_option linter.unusedSimpArgs false in
theorem run_dispatchCarry_zero (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcarry : (topCarry s dst count).toNat = 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchCarryPath
      (entry s dst modulus count returnDest rest) =
      some (topLoaded s dst modulus count returnDest rest 1602) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have h1618 : (1618 : UInt256) = UInt256.ofNat 1618 := by decide
  have h1618Nat : (1618 : UInt256).toNat = 1618 := by decide
  have hcarryExpanded :
      ((MachineState.readWord s.memory
          ((dst.toNat +
            ((UInt256.ofNat count - 1).shiftLeft (UInt256.ofNat 5)).toNat) %
              (2 ^ 256))).shiftRight
            (UInt256.ofNat 255)).toNat = 0 := by
    simpa only [topCarry, topWord, topOffset,
      Challenge.EvmProof.Word.word_toNat_add] using hcarry
  norm_num at hcarryExpanded
  simp [dispatchCarryPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entry, topLoaded, topOffset, topCarry, topWord, dispatchCarryPCs, hrun,
    hcarry, hcarryExpanded, hfive, h255,
    hc6, hc7, hc8, hc9, hc10, UInt256.isTrue, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_dispatchCarry_nonzero (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcarry : ¬ (topCarry s dst count).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchCarryPath
      (entry s dst modulus count returnDest rest) =
      some (topLoaded s dst modulus count returnDest rest 1618) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have h1618 : (1618 : UInt256) = UInt256.ofNat 1618 := by decide
  have h1618Nat : (1618 : UInt256).toNat = 1618 := by decide
  have hcarryExpanded : ¬
      ((MachineState.readWord s.memory
          ((dst.toNat +
            ((UInt256.ofNat count - 1).shiftLeft (UInt256.ofNat 5)).toNat) %
              (2 ^ 256))).shiftRight
            (UInt256.ofNat 255)).toNat = 0 := by
    simpa only [topCarry, topWord, topOffset,
      Challenge.EvmProof.Word.word_toNat_add] using hcarry
  norm_num at hcarryExpanded
  simp [dispatchCarryPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entry, topLoaded, topOffset, topCarry, topWord, dispatchCarryPCs, hrun, hcarry,
    hcode, jump1618, hc6, hc7, hc8, hc9, hc10, hcarryExpanded, hfive, h255,
    h1618, h1618Nat,
    UInt256.isTrue,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_dispatchCompare_safe (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006)
    (hsafe : (topSum s dst count).toNat < (modulusTop s modulus count).toNat)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchComparePath
      (topLoaded s dst modulus count returnDest rest 1602) =
      some (topCompared s dst modulus count returnDest rest 1625) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp only [topSum, topWord, modulusTop, topOffset,
    Challenge.EvmProof.Word.word_toNat_add] at hsafe
  norm_num at hsafe
  have h1625 : (1625 : UInt256) = UInt256.ofNat 1625 := by decide
  have h1625Nat : (1625 : UInt256).toNat = 1625 := by decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp only [honeNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at hsafe
  simp [dispatchComparePath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topLoaded, topCompared, topOffset, topSum, topWord, modulusTop, dispatchComparePCs,
    hrun, hcode, hsafe, jump1625, h1625, h1625Nat, honeNat,
    hc8, hc9, hc10, hc11,
    UInt256.isTrue,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_dispatchCompare_unsafe (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006)
    (hunsafe : ¬ (topSum s dst count).toNat < (modulusTop s modulus count).toNat)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchComparePath
      (topLoaded s dst modulus count returnDest rest 1602) =
      some (topCompared s dst modulus count returnDest rest 1618) := by
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp only [topSum, topWord, modulusTop, topOffset,
    Challenge.EvmProof.Word.word_toNat_add] at hunsafe
  norm_num at hunsafe
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp only [honeNat, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at hunsafe
  simp [dispatchComparePath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topLoaded, topCompared, topOffset, topSum, topWord, modulusTop, dispatchComparePCs,
    hrun, hunsafe, jump1618, honeNat, hc8, hc9, hc10, hc11,
    UInt256.isTrue,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, List.exchange,
    Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_dispatchUnsafe_loaded (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchUnsafePath
      (topLoaded s dst modulus count returnDest rest 1618) =
      some (fusedEntry
        (topLoaded s dst modulus count returnDest rest 1618)
        dst modulus count returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1632Nat : (1632 : UInt256).toNat = 1632 := by decide
  have h1632 : (1632 : UInt256) = UInt256.ofNat 1632 := by decide
  simp [dispatchUnsafePath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topLoaded, fusedEntry, dispatchUnsafePCs, hrun, hcode, jump1632, h1632Nat,
    h1632,
    hc6, hc7, hc8, hc9, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_dispatchUnsafe_compared (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchUnsafePath
      (topCompared s dst modulus count returnDest rest 1618) =
      some (fusedEntry
        (topCompared s dst modulus count returnDest rest 1618)
        dst modulus count returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h1632Nat : (1632 : UInt256).toNat = 1632 := by decide
  have h1632 : (1632 : UInt256) = UInt256.ofNat 1632 := by decide
  simp [dispatchUnsafePath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topCompared, topLoaded, fusedEntry, dispatchUnsafePCs, hrun, hcode, jump1632,
    h1632Nat, h1632,
    hc6, hc7, hc8, hc9, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_dispatchSafe (s : State) (dst modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock dispatchSafePath
      (topCompared s dst modulus count returnDest rest 1625) =
      some (addEntry (topCompared s dst modulus count returnDest rest 1625)
        dst modulus count returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h1473Nat : (1473 : UInt256).toNat = 1473 := by decide
  have h1473 : (1473 : UInt256) = UInt256.ofNat 1473 := by decide
  simp [dispatchSafePath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    topCompared, topLoaded, addEntry, dispatchSafePCs, hrun, hcode, jump1473,
    h1473Nat, h1473,
    hc6, hc7, hc8, hc9, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_fusedSetup (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedSetupPath
      (fusedEntry s dst modulus count returnDest rest) =
      some (fusedLoop s dst modulus count 0 returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [fusedSetupPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedEntry, fusedLoop, fusedProgress, fusedSetupPCs, hrun, hone, hzero,
    hzeroRaw, hc4, hc5, hc6, hc7, hc8, hc9, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_fusedGuard (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcount : count < 2 ^ 256) (hi : i < count)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedGuardPath
      (fusedLoop s dst modulus count i returnDest rest) =
      some (fusedBodyEntry s dst modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hiMod : i % 2 ^ 256 = i := Nat.mod_eq_of_lt hi256
  have hcountMod : count % 2 ^ 256 = count := Nat.mod_eq_of_lt hcount
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat count) = 1 := by
    have hlt' : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat count) =
        UInt256.ofNat 1 := by
      apply Challenge.EvmProof.Word.word_ext
      simp only [UInt256.lt]
      rw [Challenge.EvmProof.Word.word_toNat_ofNat,
        Challenge.EvmProof.Word.word_toNat_ofNat, hiMod, hcountMod, if_pos hi]
    exact hlt'.trans (by decide)
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  have hltNat : (UInt256.lt (UInt256.ofNat i) (UInt256.ofNat count)).toNat = 1 := by
    rw [hlt]
    exact honeNat
  have hpc : (UInt256.ofNat 1644 + UInt256.ofNat 3).succ = UInt256.ofNat 1648 := by
    decide
  have hbranch :
      (if i % 2 ^ 256 < count % 2 ^ 256 then UInt256.ofNat 1
        else UInt256.ofNat 0).toNat = (1 : UInt256).toNat := by
    rw [hiMod, hcountMod, if_pos hi]
    decide
  have hbranchOne :
      (if i % 2 ^ 256 < count % 2 ^ 256 then UInt256.ofNat 1
        else UInt256.ofNat 0).toNat = 1 := hbranch.trans honeNat
  have hbranchLiteral := hbranchOne
  norm_num at hbranchLiteral
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [fusedGuardPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedLoop, fusedBodyEntry, fusedGuardPCs, hrun, hlt, hltNat, honeNat, hpc,
    hi, hi256, hcount, hiMod, hcountMod, hbranch, hbranchOne, hbranchLiteral,
    hc7, hc8, hc9, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, UInt256.lt]

set_option linter.unusedSimpArgs false in
theorem run_fusedFinishGuard (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedGuardPath
      (fusedLoop s dst modulus count count returnDest rest) =
      some (fusedAtFinish s dst modulus count returnDest rest 1718) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h1718 : (1718 : UInt256) = UInt256.ofNat 1718 := by decide
  have h1718Nat : (1718 : UInt256).toNat = 1718 := by decide
  simp [fusedGuardPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedLoop, fusedAtFinish, fusedGuardPCs, hrun, hcode, jump1718, h1718,
    h1718Nat,
    hc7, hc8, hc9, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_fusedBody (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedBodyPath
      (fusedBodyEntry s dst modulus count i returnDest rest) =
      some (fusedLoop s dst modulus count (i + 1) returnDest rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    (Challenge.EvmProof.Word.word_add_comm _ _).trans hinc
  let progress := fusedProgress s.memory s.activeWords dst modulus i
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have h1639 : (1639 : UInt256) = UInt256.ofNat 1639 := by decide
  have h1639Nat : (1639 : UInt256).toNat = 1639 := by decide
  have h5120Nat : (5120 : UInt256).toNat = 5120 := by decide
  have hdstOffset :
      (dst.toNat + ((UInt256.ofNat i).shiftLeft (UInt256.ofNat 5)).toNat) %
          2 ^ 256 < 2 ^ 256 := by
    exact Nat.mod_lt _ (by positivity)
  have hactiveDst := activeWordsAfter32_mod_idem_nat
    (fusedProgress s.memory s.activeWords dst modulus i).activeWords.toNat
    ((dst.toNat + ((UInt256.ofNat i).shiftLeft (UInt256.ofNat 5)).toNat) %
      2 ^ 256)
    (fusedProgress s.memory s.activeWords dst modulus i).activeWords.val.isLt
    hdstOffset
  have hactiveDstLiteral := hactiveDst
  norm_num at hactiveDstLiteral
  have hactiveDstLt : MachineState.activeWordsAfter
      (fusedProgress s.memory s.activeWords dst modulus i).activeWords.toNat
      ((dst.toNat + ((UInt256.ofNat i).shiftLeft (UInt256.ofNat 5)).toNat) %
        2 ^ 256) 32 < 2 ^ 256 := by
    have h := activeWordsAfter32_lt
      (fusedProgress s.memory s.activeWords dst modulus i).activeWords
      (UInt256.ofNat ((dst.toNat +
        ((UInt256.ofNat i).shiftLeft (UInt256.ofNat 5)).toNat) % 2 ^ 256))
    simpa [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hdstOffset] using h
  have hvalid : Decode.isValidJumpDest submissionBytecode
      (1639 : UInt256).toNat = true := by
    rw [h1639Nat]
    exact jump1639
  simp (config := { maxSteps := 1200000 })
    [fusedBodyPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
      List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      fusedBodyEntry, fusedLoop, fusedProgress, progress, off, fusedBodyPCs,
      hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18,
      hcode, hrun, hinc, hincLeft, hvalid, h1639, h1639Nat, h5120Nat,
      hactiveDst, hactiveDstLiteral, jump1639,
      hone, hfive, h255, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      activeWordsAfter32_idem, activeWordsAfter32_mod_idem, activeWordsAfter32_word_idem,
      activeWordsAfter32_word_twice_eq_thrice,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_fusedFinish_skip (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006)
    (hskip : (fusedUseSub s dst modulus count).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedFinishPath
      (fusedAtFinish s dst modulus count returnDest rest 1718) =
      some (fusedChoice s dst modulus count returnDest rest 1738) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp only [fusedUseSub, Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_isZero] at hskip
  have h1738 : (1738 : UInt256) = UInt256.ofNat 1738 := by decide
  have h1738Nat : (1738 : UInt256).toNat = 1738 := by decide
  simp [fusedFinishPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedAtFinish, fusedChoice, fusedUseSub, fusedFinishPCs, hskip, hcode, hrun,
    h1738, h1738Nat,
    jump1738, hc6, hc7, hc8, hc9, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_fusedFinish_copy (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006)
    (hcopy : ¬ (fusedUseSub s dst modulus count).toNat = 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedFinishPath
      (fusedAtFinish s dst modulus count returnDest rest 1718) =
      some (fusedChoice s dst modulus count returnDest rest 1729) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp only [fusedUseSub, Challenge.EvmProof.Word.word_toNat_lor,
    Challenge.EvmProof.Word.word_toNat_isZero] at hcopy
  have hpc : (UInt256.ofNat 1725 + UInt256.ofNat 3).succ =
      UInt256.ofNat 1729 := by decide
  simp [fusedFinishPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedAtFinish, fusedChoice, fusedUseSub, fusedFinishPCs, hcopy, hrun, hpc,
    hc6, hc7, hc8, hc9, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_fusedCopy (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedCopyPath
      (fusedChoice s dst modulus count returnDest rest 1729) =
      some (fusedCopied s dst modulus count returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have hfiveK : (5120 : UInt256) = UInt256.ofNat 5120 := by decide
  have hfiveKNat : (5120 : UInt256).toNat = 5120 := by decide
  simp [fusedCopyPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedChoice, fusedCopied, BigHelpers.mcopySize, fusedCopyPCs,
    hc6, hc7, hc8, hc9, hc10, hrun, hfive, hfiveK, hfiveKNat,
    State.activeWordsAfterUInt256_2,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_fusedExit_skip (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006)
    (hskip : (fusedUseSub s dst modulus count).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedExitPath
      (fusedChoice s dst modulus count returnDest rest 1738) =
      some (fusedReturned s dst modulus count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  unfold fusedReturned
  dsimp only
  rw [show BigHelpers.maskChoice
      (fusedProgress s.memory s.activeWords dst modulus count).memory
      (fusedProgress s.memory s.activeWords dst modulus count).activeWords dst
      (0 - fusedUseSub s dst modulus count) count =
      ⟨(fusedProgress s.memory s.activeWords dst modulus count).memory,
       (fusedProgress s.memory s.activeWords dst modulus count).activeWords⟩ by
    apply BigHelpers.maskChoice_of_zero
    exact BigHelpers.mask_toNat_of_zero _ hskip]
  simp [fusedExitPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedChoice, fusedReturned, fusedUseSub, fusedExitPCs,
    hc1, hc2, hc3, hc4, hc5, hc6, hcode, hvalid, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_fusedExit_copy (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006)
    (hcopy : ¬ (fusedUseSub s dst modulus count).toNat = 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fusedExitPath
      (fusedCopied s dst modulus count returnDest rest) =
      some (fusedReturned s dst modulus count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have huseLe : (fusedUseSub s dst modulus count).toNat ≤ 1 := by
    simpa only [fusedUseSub] using BigHelpers.useSub_toNat_le_one
      (fusedProgress s.memory s.activeWords dst modulus count).carry
      (fusedProgress s.memory s.activeWords dst modulus count).borrow
      (fusedProgress_carry_le_one s.memory s.activeWords dst modulus count)
      (fusedProgress_borrow_le_one s.memory s.activeWords dst modulus count)
  have huseOne : (fusedUseSub s dst modulus count).toNat = 1 := by omega
  have hmask : ¬ (0 - fusedUseSub s dst modulus count).toNat = 0 := by
    exact BigHelpers.mask_toNat_of_one
      (fusedUseSub s dst modulus count)
      huseOne
  unfold fusedReturned
  dsimp only
  rw [BigHelpers.maskChoice_of_pos _ _ _ _ _ hmask]
  simp [fusedExitPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fusedCopied, fusedChoice, fusedReturned, fusedUseSub, fusedExitPCs,
    BigHelpers.mcopySize, hc1, hc2, hc3, hc4, hc5, hc6,
    hcode, hvalid, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

private theorem addProgress_carry_le_one (memory : ByteArray)
    (activeWords dst src mask : UInt256) (i : Nat) :
    (BigHelpers.addProgress memory activeWords dst src mask i).carry.toNat ≤ 1 := by
  induction i with
  | zero =>
      simp only [BigHelpers.addProgress]
      decide
  | succ i ih =>
      let before := BigHelpers.addProgress memory activeWords dst src mask i
      let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
      let x := MachineState.readWord before.memory (dst + off).toNat
      let y := UInt256.land (MachineState.readWord before.memory (src + off).toNat) mask
      have hstep := BigHelpers.addLimbStep_toNat x y before.carry (by simpa [before] using ih)
      simp only [BigHelpers.addProgress]
      rw [hstep.2]
      have hx : x.toNat < 2 ^ 256 := x.val.isLt
      have hy : y.toNat < 2 ^ 256 := y.val.isLt
      have hc : before.carry.toNat ≤ 1 := by simpa [before] using ih
      have htotal : x.toNat + y.toNat + before.carry.toNat <
          2 * Limbs.radix := by
        simp only [Limbs.radix]
        omega
      have hdiv : (x.toNat + y.toNat + before.carry.toNat) /
          Limbs.radix < 2 := by
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using htotal)
      omega

private theorem land_neg_one (x : UInt256) : UInt256.land x (0 - 1) = x := by
  apply Challenge.EvmProof.Word.word_ext
  have h := BigHelpers.land_sub_zero_take_toNat x (take := 1) (by omega)
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simpa only [hone, Nat.one_mul] using h

private theorem doubleCarry_eq (x carry : UInt256)
    (hcarry : carry.toNat ≤ 1) :
    UInt256.shiftRight x (UInt256.ofNat 255) =
      UInt256.lor (UInt256.lt (x + x) x)
        (UInt256.lt ((x + x) + carry) (x + x)) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.shiftRight_toNat x (by omega)]
  rw [(BigHelpers.addLimbStep_toNat x x carry hcarry).2]
  rw [Nat.shiftRight_eq_div_pow]
  change x.toNat / 2 ^ 255 =
    (x.toNat + x.toNat + carry.toNat) / 2 ^ 256
  have hxlt : x.toNat < 2 ^ 256 := x.val.isLt
  have hpow : 2 ^ 256 = 2 * 2 ^ 255 := by norm_num [pow_succ]
  by_cases hx : x.toNat < 2 ^ 255
  · have htotal : x.toNat + x.toNat + carry.toNat < 2 ^ 256 := by
      omega
    rw [Nat.div_eq_of_lt hx, Nat.div_eq_of_lt htotal]
  · have hxle : 2 ^ 255 ≤ x.toNat := by omega
    have htotalLe : 2 ^ 256 ≤ x.toNat + x.toNat + carry.toNat := by omega
    have htotalLt : x.toNat + x.toNat + carry.toNat < 2 * 2 ^ 256 := by omega
    have hxdiv : x.toNat / 2 ^ 255 = 1 := by
      apply Nat.div_eq_of_lt_le
      · exact hxle
      · omega
    have htotaldiv : (x.toNat + x.toNat + carry.toNat) / 2 ^ 256 = 1 := by
      apply Nat.div_eq_of_lt_le
      · exact htotalLe
      · exact htotalLt
    rw [hxdiv, htotaldiv]

set_option linter.unusedSimpArgs false in
theorem run_setup (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addSetupPath
      (addEntry s dst modulus count returnDest rest) =
        some (loop s dst modulus count 0 returnDest rest) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzero' : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp [addSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    addEntry, loop, BigHelpers.addProgress, addSetupPCs, hc6, hc7, hc8, hc9,
    hrun, hzero, hzero',
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt]

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcount : count < 2 ^ 256)
    (hi : i < count) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addGuardPath
      (loop s dst modulus count i returnDest rest) =
        some (bodyEntry s dst modulus count i returnDest rest) := by
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hne : ¬ i % 2 ^ 256 = count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    omega
  have hneLiteral :
      ¬ i % 115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        count % 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num at hne ⊢
    exact hne
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [addGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loop, bodyEntry, addGuardPCs, hc9, hc10, hc11, hrun,
    UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hne, hneLiteral]

set_option linter.unusedSimpArgs false in
theorem run_body (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addBodyPath
      (bodyEntry s dst modulus count i returnDest rest) =
        some (loop s dst modulus count (i + 1) returnDest rest) := by
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    (Challenge.EvmProof.Word.word_add_comm _ _).trans hinc
  let progress := BigHelpers.addProgress s.memory s.activeWords dst dst
    (0 - 1) i
  let off := UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)
  let x := MachineState.readWord progress.memory (dst + off).toNat
  have hcarry : progress.carry.toNat ≤ 1 := by
    exact addProgress_carry_le_one s.memory s.activeWords dst dst (0 - 1) i
  have hcarryEq := doubleCarry_eq x progress.carry hcarry
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have h1479 : (1479 : UInt256) = UInt256.ofNat 1479 := by decide
  have h1479Nat : (1479 : UInt256).toNat = 1479 := by decide
  have hvalid : Decode.isValidJumpDest submissionBytecode
      (1479 : UInt256).toNat = true := by
    rw [h1479Nat]
    exact jump1479
  have hland : UInt256.land x (0 - UInt256.ofNat 1) = x := by
    rw [← hone]
    exact land_neg_one x
  have hmaskNat : x.toNat &&& (2 ^ 256 - 1) = x.toNat :=
    (Nat.and_two_pow_sub_one_eq_mod x.toNat 256).trans
      (Nat.mod_eq_of_lt x.val.isLt)
  have hzeroNat : (0 : UInt256).toNat = 0 := by decide
  simp (config := { maxSteps := 800000 })
    [addBodyPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bodyEntry, loop, BigHelpers.addProgress, progress, off, x,
      addBodyPCs, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
      hcode, hrun, hinc, hincLeft, hcarryEq, hland, land_neg_one, hvalid,
      h1479, h1479Nat, jump1479,
      hone, hfive, h255, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      activeWordsAfter32_idem, activeWordsAfter32_word_idem,
      activeWordsAfter32_word_twice_eq_thrice,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      List.exchange]
  constructor
  · constructor
    · simpa [progress, off, hone] using
        (activeWordsAfter32_word_twice_eq_thrice progress.activeWords (dst + off))
    · rw [← hone]
      norm_num [hzeroNat]
      change MachineState.writeBytes progress.memory
          (Data.Bytes.natToBytesPadded
            ((progress.carry.toNat + (x.toNat + x.toNat)) % 2 ^ 256) 32)
          (dst + off).toNat =
        MachineState.writeBytes progress.memory
          (Data.Bytes.natToBytesPadded
            ((progress.carry.toNat +
              (x.toNat + (x.toNat &&& (2 ^ 256 - 1)))) % 2 ^ 256) 32)
          (dst + off).toNat
      rw [hmaskNat]
  · change UInt256.shiftRight x (UInt256.ofNat 255) =
      UInt256.lor (UInt256.lt (x + UInt256.land x (0 - UInt256.ofNat 1)) x)
        (UInt256.lt
          ((x + UInt256.land x (0 - UInt256.ofNat 1)) + progress.carry)
          (x + UInt256.land x (0 - UInt256.ofNat 1)))
    rw [hland]
    exact hcarryEq

set_option linter.unusedSimpArgs false in
theorem run_finish_guard (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock addGuardPath
      (loop s dst modulus count count returnDest rest) =
      some { BigHelpers.addLoop s dst dst 1 modulus count count returnDest rest with
        pc := UInt256.ofNat 1745 } := by
  have hdest : (1745 : UInt256) = UInt256.ofNat 1745 := by decide
  have hdestNat : (1745 : UInt256).toNat = 1745 := by decide
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  simp [addGuardPath, opAt, pushAt, wfOp, loop, BigHelpers.addLoop, addGuardPCs,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hc9, hc10, hc11, hcode, hrun, UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hdest, hdestNat, jump1745]

set_option linter.unusedSimpArgs false in
theorem run_fastExit (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1006) (hcode : s.executionEnv.code = submissionBytecode)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fastExitPath
      { BigHelpers.addLoop s dst dst 1 modulus count count returnDest rest with
        pc := UInt256.ofNat 1745 } =
      some (addOnlyReturned s dst modulus count returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  simp [fastExitPath, fusedBlock, locateSlice, fusedInstructionsLiteral,
    List.ofFn, Fin.foldr, Fin.foldr.loop, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    BigHelpers.addLoop, addOnlyReturned, fastExitPCs, hc1, hc2, hc3, hc4, hc5, hc6, hc7,
    hc8, hc9, hcode, hvalid, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_setup (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst modulus count returnDest rest)
      (loop s dst modulus count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka addSetupPath hcode hfork
      (run_setup s dst modulus count returnDest rest (by omega) hrun) hrun hnp

def gasSteps_iteration (s : State) (dst modulus : UInt256) (count i : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loop s dst modulus count i returnDest rest)
      (loop s dst modulus count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addGuardPath
        (by simpa [loop, Artifact.submissionArtifact] using hcode)
        (by simpa [loop, State.fork] using hfork)
        (run_guard s dst modulus count i returnDest rest (by omega) hcount hi hrun)
        (by simpa [loop] using hrun)
        (by simpa [loop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka addBodyPath
        (by simpa [bodyEntry, loop, Artifact.submissionArtifact] using hcode)
        (by simpa [bodyEntry, loop, State.fork] using hfork)
        (run_body s dst modulus count i returnDest rest (by omega) (by omega)
          hcode hrun)
        (by simpa [bodyEntry, loop] using hrun)
        (by simpa [bodyEntry, loop, State.fork] using hnp))

def gasSteps_loop (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loop s dst modulus count 0 returnDest rest)
      (loop s dst modulus count count returnDest rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_iteration s dst modulus count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp

def gasSteps_fusedSetup (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (fusedEntry s dst modulus count returnDest rest)
      (fusedLoop s dst modulus count 0 returnDest rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fusedSetupPath hcode hfork
      (run_fusedSetup s dst modulus count returnDest rest (by omega) hrun) hrun hnp

def gasSteps_fusedIteration (s : State) (dst modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (fusedLoop s dst modulus count i returnDest rest)
      (fusedLoop s dst modulus count (i + 1) returnDest rest) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedGuardPath
        (by simpa [fusedLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedLoop, State.fork] using hfork)
        (run_fusedGuard s dst modulus count i returnDest rest (by omega)
          hcount hi hrun)
        (by simpa [fusedLoop] using hrun)
        (by simpa [fusedLoop, State.fork] using hnp)).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedBodyPath
        (by simpa [fusedBodyEntry, fusedLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedBodyEntry, fusedLoop, State.fork] using hfork)
        (run_fusedBody s dst modulus count i returnDest rest hcap (by omega)
          hcode hrun)
        (by simpa [fusedBodyEntry, fusedLoop] using hrun)
        (by simpa [fusedBodyEntry, fusedLoop, State.fork] using hnp))

def gasSteps_fusedLoop (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (fusedLoop s dst modulus count 0 returnDest rest)
      (fusedLoop s dst modulus count count returnDest rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_fusedIteration s dst modulus count i returnDest rest hcap hcount hi
      hcode hfork hrun hnp

def gasSteps_fused (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (fusedEntry s dst modulus count returnDest rest)
      (fusedReturned s dst modulus count returnDest rest) := by
  have hsetup := gasSteps_fusedSetup s dst modulus count returnDest rest hcap
    hcode hfork hrun hnp
  have hloop := gasSteps_fusedLoop s dst modulus count returnDest rest hcap
    hcount hcode hfork hrun hnp
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fusedGuardPath
      (by simpa [fusedLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [fusedLoop, State.fork] using hfork)
      (run_fusedFinishGuard s dst modulus count returnDest rest (by omega)
        hcode hrun)
      (by simpa [fusedLoop] using hrun)
      (by simpa [fusedLoop, State.fork] using hnp)
  by_cases huse : (fusedUseSub s dst modulus count).toNat = 0
  · have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedFinishPath
        (by simpa [fusedAtFinish, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedAtFinish, State.fork] using hfork)
        (run_fusedFinish_skip s dst modulus count returnDest rest (by omega)
          huse hcode hrun)
        (by simpa [fusedAtFinish] using hrun)
        (by simpa [fusedAtFinish, State.fork] using hnp)
    have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedExitPath
        (by simpa [fusedChoice, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedChoice, State.fork] using hfork)
        (run_fusedExit_skip s dst modulus count returnDest rest (by omega)
          huse hcode hvalid hrun)
        (by simpa [fusedChoice] using hrun)
        (by simpa [fusedChoice, State.fork] using hnp)
    exact hsetup.trans (hloop.trans (hguard.trans (hfinish.trans hexit)))
  · have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedFinishPath
        (by simpa [fusedAtFinish, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedAtFinish, State.fork] using hfork)
        (run_fusedFinish_copy s dst modulus count returnDest rest (by omega)
          huse hrun)
        (by simpa [fusedAtFinish] using hrun)
        (by simpa [fusedAtFinish, State.fork] using hnp)
    have hcopy := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedCopyPath
        (by simpa [fusedChoice, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedChoice, State.fork] using hfork)
        (run_fusedCopy s dst modulus count returnDest rest (by omega) hcode hrun)
        (by simpa [fusedChoice] using hrun)
        (by simpa [fusedChoice, State.fork] using hnp)
    have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka fusedExitPath
        (by simpa [fusedCopied, fusedChoice, Artifact.submissionArtifact] using hcode)
        (by simpa [fusedCopied, fusedChoice, State.fork] using hfork)
        (run_fusedExit_copy s dst modulus count returnDest rest (by omega)
          huse hcode hvalid hrun)
        (by simpa [fusedCopied, fusedChoice] using hrun)
        (by simpa [fusedCopied, fusedChoice, State.fork] using hnp)
    exact hsetup.trans
      (hloop.trans (hguard.trans (hfinish.trans (hcopy.trans hexit))))

def gasSteps_addOnly (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst modulus count returnDest rest)
      (addOnlyReturned s dst modulus count returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka addGuardPath
      (by simpa [loop, Artifact.submissionArtifact] using hcode)
      (by simpa [loop, State.fork] using hfork)
      (run_finish_guard s dst modulus count returnDest rest (by omega) hcode hrun)
      (by simpa [loop] using hrun)
      (by simpa [loop, State.fork] using hnp)
  have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fastExitPath
      (by simpa [BigHelpers.addLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [BigHelpers.addLoop, State.fork] using hfork)
      (run_fastExit s dst modulus count returnDest rest (by omega) hcode hvalid hrun)
      (by simpa [BigHelpers.addLoop] using hrun)
      (by simpa [BigHelpers.addLoop, State.fork] using hnp)
  exact
    (gasSteps_setup s dst modulus count returnDest rest hcap hcode hfork hrun hnp).trans <|
    (gasSteps_loop s dst modulus count returnDest rest hcap hcount hcode hfork hrun hnp).trans <|
    hguard.trans hexit

def gasSteps_doubleMod (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (entry s dst modulus count returnDest rest)
      (returned s dst modulus count returnDest rest) := by
  by_cases hcarry : (topCarry s dst count).toNat = 0
  · have hdispatch := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka dispatchCarryPath
        (by simpa [entry, Artifact.submissionArtifact] using hcode)
        (by simpa [entry, State.fork] using hfork)
        (run_dispatchCarry_zero s dst modulus count returnDest rest (by omega)
          hcarry hrun)
        (by simpa [entry] using hrun)
        (by simpa [entry, State.fork] using hnp)
    by_cases hsafe :
        (topSum s dst count).toNat < (modulusTop s modulus count).toNat
    · have hcompare := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka dispatchComparePath
          (by simpa [topLoaded, Artifact.submissionArtifact] using hcode)
          (by simpa [topLoaded, State.fork] using hfork)
          (run_dispatchCompare_safe s dst modulus count returnDest rest
            (by omega) hsafe hcode hrun)
          (by simpa [topLoaded] using hrun)
          (by simpa [topLoaded, State.fork] using hnp)
      have hcleanup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka dispatchSafePath
          (by simpa [topCompared, topLoaded, Artifact.submissionArtifact] using hcode)
          (by simpa [topCompared, topLoaded, State.fork] using hfork)
          (run_dispatchSafe s dst modulus count returnDest rest (by omega)
            hcode hrun)
          (by simpa [topCompared, topLoaded] using hrun)
          (by simpa [topCompared, topLoaded, State.fork] using hnp)
      have hadd := gasSteps_addOnly
        (topCompared s dst modulus count returnDest rest 1625)
        dst modulus count returnDest rest hcap hcount
        (by simpa [topCompared, topLoaded] using hcode)
        (by simpa [topCompared, topLoaded, State.fork] using hfork)
        (by simpa [topCompared, topLoaded] using hrun)
        (by simpa [topCompared, topLoaded, State.fork] using hnp) hvalid
      simpa [returned, hcarry, hsafe] using
        hdispatch.trans (hcompare.trans (hcleanup.trans hadd))
    · have hcompare := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka dispatchComparePath
          (by simpa [topLoaded, Artifact.submissionArtifact] using hcode)
          (by simpa [topLoaded, State.fork] using hfork)
          (run_dispatchCompare_unsafe s dst modulus count returnDest rest
            (by omega) hsafe hcode hrun)
          (by simpa [topLoaded] using hrun)
          (by simpa [topLoaded, State.fork] using hnp)
      have hcleanup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka dispatchUnsafePath
          (by simpa [topCompared, topLoaded, Artifact.submissionArtifact] using hcode)
          (by simpa [topCompared, topLoaded, State.fork] using hfork)
          (run_dispatchUnsafe_compared s dst modulus count returnDest rest
            (by omega) hcode hrun)
          (by simpa [topCompared, topLoaded] using hrun)
          (by simpa [topCompared, topLoaded, State.fork] using hnp)
      have hfused := gasSteps_fused
        (topCompared s dst modulus count returnDest rest 1618)
        dst modulus count returnDest rest hcap hcount
        (by simpa [topCompared, topLoaded] using hcode)
        (by simpa [topCompared, topLoaded, State.fork] using hfork)
        (by simpa [topCompared, topLoaded] using hrun)
        (by simpa [topCompared, topLoaded, State.fork] using hnp) hvalid
      simpa [returned, hcarry, hsafe] using
        hdispatch.trans (hcompare.trans (hcleanup.trans hfused))
  · have hdispatch := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka dispatchCarryPath
        (by simpa [entry, Artifact.submissionArtifact] using hcode)
        (by simpa [entry, State.fork] using hfork)
        (run_dispatchCarry_nonzero s dst modulus count returnDest rest
          (by omega) hcarry hcode hrun)
        (by simpa [entry] using hrun)
        (by simpa [entry, State.fork] using hnp)
    have hcleanup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka dispatchUnsafePath
        (by simpa [topLoaded, Artifact.submissionArtifact] using hcode)
        (by simpa [topLoaded, State.fork] using hfork)
        (run_dispatchUnsafe_loaded s dst modulus count returnDest rest
          (by omega) hcode hrun)
        (by simpa [topLoaded] using hrun)
        (by simpa [topLoaded, State.fork] using hnp)
    have hfused := gasSteps_fused
      (topLoaded s dst modulus count returnDest rest 1618)
      dst modulus count returnDest rest hcap hcount
      (by simpa [topLoaded] using hcode)
      (by simpa [topLoaded, State.fork] using hfork)
      (by simpa [topLoaded] using hrun)
      (by simpa [topLoaded, State.fork] using hnp) hvalid
    simpa [returned, hcarry] using hdispatch.trans (hcleanup.trans hfused)

/- Retired composition through the general subtraction tail.
def gasSteps_toSubtract (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loop s dst modulus count count returnDest rest)
      (BigHelpers.subtractLoop s dst dst 1 modulus count 0 returnDest rest) := by
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka addGuardPath
      (by simpa [loop, Artifact.submissionArtifact] using hcode)
      (by simpa [loop, State.fork] using hfork)
      (run_finish_guard s dst modulus count returnDest rest (by omega) hcode hrun)
      (by simpa [loop] using hrun)
      (by simpa [loop, State.fork] using hnp)
  have htransition := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka BigHelpers.addToSubtractPath
      (by simpa [BigHelpers.addLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [BigHelpers.addLoop, State.fork] using hfork)
      (BigHelpers.run_addToSubtract s dst dst 1 modulus count returnDest rest
        (by omega) hrun)
      (by simpa [BigHelpers.addLoop] using hrun)
      (by simpa [BigHelpers.addLoop, State.fork] using hnp)
  have hzero : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simpa [BigHelpers.subtractLoop, BigHelpers.subtractLoopEntry,
    BigHelpers.subtractProgress, hzero] using hguard.trans htransition

def gasSteps_doubleMod (s : State) (dst modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode) (hfork : s.fork = .Osaka)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (addEntry s dst modulus count returnDest rest)
      (BigHelpers.addReturned s dst dst 1 modulus count returnDest rest) :=
  (gasSteps_setup s dst modulus count returnDest rest hcap hcode hfork hrun hnp).trans <|
  (gasSteps_loop s dst modulus count returnDest rest hcap hcount hcode hfork hrun hnp).trans <|
  (gasSteps_toSubtract s dst modulus count returnDest rest hcap hcode hfork hrun hnp).trans <|
  (BigHelpers.gasSteps_subtractLoop s dst dst 1 modulus count returnDest rest
    hcap hcount hcode hfork hrun hnp).trans <|
  (BigHelpers.gasSteps_subtractFinish s dst dst 1 modulus count returnDest rest
    hcap hcode hfork hrun hnp).trans <|
  (BigHelpers.gasSteps_addMaskSegment s dst dst 1 modulus count returnDest rest
    hcap hcount hcode hfork hrun hnp).trans <|
  BigHelpers.gasSteps_addExit s dst dst 1 modulus count returnDest rest hcap
    hcode hfork hrun hnp hvalid
-/

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDouble
