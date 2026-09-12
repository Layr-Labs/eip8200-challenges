import Challenge.Ripemd160.Submission.Proofs.Bytecode.KnownInputLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanMask
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompactGuardConstants
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanState

set_option warningAsError true
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option linter.unusedSimpArgs false

/-!
# The scan states of the scalar-SWAR guard

The five constants stay on the stack for the whole scan, so a loop state is
those five under the running scalar, offset and accumulator.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

/-- The stepper writes `*`; the recurrence writes `UInt256.mul`. -/
@[simp] theorem mul_eq (a b : UInt256) : a * b = UInt256.mul a b := rfl

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod
  Challenge.EvmProof.Word.word_toNat_ofNat

def atPC (input : ByteArray) (pc : Nat) : State :=
  { initialState submissionBytecode input 0 with pc := UInt256.ofNat pc }

/-! Only these projections of the initial state are ever unfolded, so `simp`
never normalizes the 5298-byte array. -/

@[simp] theorem initialState_code (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).executionEnv.code = code := rfl

@[simp] theorem initialState_halt (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).halt = .Running := rfl

@[simp] theorem initialState_memory (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).memory = ByteArray.empty := rfl

@[simp] theorem initialState_activeWords (code calldata : ByteArray) (gas : Nat) :
    (initialState code calldata gas).activeWords = 0 := rfl

attribute [local simp] Challenge.Ripemd160.initialState_stack
  Challenge.Ripemd160.initialState_pc
  Challenge.Ripemd160.initialState_calldata

/-- The constants the setup leaves below the working values. -/
def frame : List UInt256 := [P7, M, m7, P, m8]

def maskShift (input : ByteArray) (offset : UInt256) : UInt256 :=
  TailProjectionInstances.rawShift input.size offset

/-- The accumulator after individually masking each word difference. -/
def scanAcc (input : ByteArray) : Nat → UInt256
  | 0 => 0
  | k + 1 => UInt256.lor (scanAcc input k)
      (UInt256.shiftRight (UInt256.xor (MachineState.readWord input (32 * k)) (guardWord k))
        (maskShift input (UInt256.ofNat (32 * k))))

/-- At the head of the scan with `k` words folded in. -/
def loopState (input : ByteArray) (k : Nat) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 152
    stack := UInt256.ofNat (scalarAt k) :: UInt256.ofNat (32 * k) :: a :: frame }

/-- After the expected word is derived and any correction applied.  A
straddling word has already bumped the scalar by eleven, so it is explicit. -/
def compareState (input : ByteArray) (k s : Nat) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 207
    stack := guardWord k :: UInt256.mul M (UInt256.ofNat (scalarAt k)) ::
      UInt256.ofNat s :: UInt256.ofNat (32 * k) :: a :: frame }

/-- At the head of the correction block, for a straddling offset. -/
def straddleState (input : ByteArray) (k : Nat) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 175
    stack := rawWord k :: UInt256.mul M (UInt256.ofNat (scalarAt k)) ::
      UInt256.ofNat (scalarAt k) :: UInt256.ofNat (32 * k) :: a :: frame }

/-- After the thirty-one words, at the padded tail. -/
def tailState (input : ByteArray) (a : UInt256) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 250
    stack := UInt256.ofNat (scalarAt 32) :: UInt256.ofNat 1024 :: a :: frame }

/-- The stub jumps here, and the guard answers or falls through.  -/
def patternedEntry (input : ByteArray) : State := atPC input 100

def hitRest : List UInt256 :=
  UInt256.ofNat (scalarAt 32) :: UInt256.ofNat 1024 :: 0 :: frame

def hitState (input : ByteArray) : State :=
  { atPC input 255 with stack := hitRest }
def fallbackState (input : ByteArray) : State := atPC input 268

def storeWord (memory : ByteArray) (address : Nat) (word : UInt256) : ByteArray :=
  MachineState.writeBytes memory (Data.Bytes.natToBytesPadded word.toNat 32) address

def answerMemory : ByteArray := storeWord ByteArray.empty 0 paddedDigestWord

def returnedState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4865
    stack := hitRest
    memory := answerMemory
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded answerMemory 0 32 }

def sound (path : List Located) {s t : State}
    (h : run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
