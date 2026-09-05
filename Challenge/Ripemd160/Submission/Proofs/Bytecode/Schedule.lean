import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Direct bytecode trace for the RIPEMD-160 message schedule

The reference schedule has one sixteen-iteration loop.  Each iteration calls
the compiled `readLE32` and `xSet` helpers, loading four message bytes and
storing the resulting 32-bit word in the dedicated `X[i]` slot.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def loadOffsetWord (msgOff : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 2) + msgOff

def xSlotWord (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + UInt256.ofNat 0x2a0

def readLEWord (memory : ByteArray) (off : UInt256) : UInt256 :=
  let w := MachineState.readWord memory off.toNat
  UInt256.lor
    (UInt256.lor (UInt256.byteAt ⟨0⟩ w)
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 1) w)
        (UInt256.ofNat 8)))
    (UInt256.lor
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 2) w)
        (UInt256.ofNat 16))
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 3) w)
        (UInt256.ofNat 24)))

def scheduleEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0x236
           stack := [msgOff, returnDest] ++ rest }

def loopAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x238
           stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x242
           stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def readEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x1b7
           stack := [loadOffsetWord msgOff i, 0, UInt256.ofNat 0x253,
             UInt256.ofNat 0x259, UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterRead (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x253
           stack := [readLEWord s.memory (loadOffsetWord msgOff i),
             UInt256.ofNat 0x259, UInt256.ofNat i, msgOff, returnDest] ++ rest
           activeWords := s.activeWordsAfterUInt256
             (loadOffsetWord msgOff i).toNat 32 }

def beforeFirstByte (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let off := loadOffsetWord msgOff i
  let w := MachineState.readWord s.memory off.toNat
  { s with
    pc := UInt256.ofNat 0x1bd
    stack := [UInt256.ofNat 3, w, w, off, 0, UInt256.ofNat 0x253,
      UInt256.ofNat 0x259, UInt256.ofNat i, msgOff, returnDest] ++ rest
    activeWords := s.activeWordsAfterUInt256 off.toNat 32 }

def xSetEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let loaded := afterRead s msgOff returnDest rest i
  { loaded with
    pc := UInt256.ofNat 0x5f
    stack := [UInt256.ofNat i,
        readLEWord s.memory (loadOffsetWord msgOff i), UInt256.ofNat 0x259,
        UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let loaded := afterRead s msgOff returnDest rest i
  let value := UInt256.land (readLEWord s.memory (loadOffsetWord msgOff i))
    (UInt256.ofNat 0xffffffff)
  { loaded with
    pc := UInt256.ofNat 0x259
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes loaded.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (xSlotWord i).toNat
    activeWords := loaded.activeWordsAfterUInt256 (xSlotWord i).toNat 32 }

def afterIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { afterStore s msgOff returnDest rest i with
      pc := UInt256.ofNat 0x238
      stack := [UInt256.ofNat (i + 1), msgOff, returnDest] ++ rest }

def loopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => loopAt s msgOff returnDest rest 0
  | i + 1 => afterIteration (loopState s msgOff returnDest rest i)
      msgOff returnDest rest i

@[simp] theorem loopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (loopState s msgOff returnDest rest i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopState, afterIteration, afterStore, afterRead, ih]

@[simp] theorem loopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (loopState s msgOff returnDest rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopState, afterIteration, afterStore, afterRead, ih]

@[simp] theorem loopAt_loopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    loopAt (loopState s msgOff returnDest rest i) msgOff returnDest rest i =
      loopState s msgOff returnDest rest i := by
  cases i <;> rfl

def afterExitCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0x264
    stack := [UInt256.ofNat 16, msgOff, returnDest] ++ rest }

def scheduleReturned (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest, stack := rest }

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
