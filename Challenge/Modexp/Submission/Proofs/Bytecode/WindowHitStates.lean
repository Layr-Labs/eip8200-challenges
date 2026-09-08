import Challenge.Modexp.Submission.Proofs.Bytecode.WindowControlDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowMath
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory

set_option warningAsError true

/-!
# Fixed-width window hit boundary states

Gas-erased boundaries for the zero-modulus exit, table construction, four-byte
loop, and normal return.  These definitions mirror the stack convention of
the appended body while keeping its execution traces in smaller modules.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitStates

open EvmSemantics
open EvmSemantics.EVM
open WindowControlDefs

def baseWord (input : ByteArray) : UInt256 := MachineState.readWord input 96
def exponentWord (input : ByteArray) (offset : Nat) : UInt256 :=
  MachineState.readWord input offset
def modulusWord (input : ByteArray) : UInt256 := MachineState.readWord input 160

abbrev storeWord := WindowTableMemory.storeWord

abbrev tableWord := WindowMath.tableWord

abbrev tableMemoryThrough := WindowTableMemory.tableMemoryThrough

abbrev tableMemory := WindowTableMemory.tableMemory

/-- Nonzero-modulus branch boundary before loading the base. -/
def nonzeroState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 3034
    stack := modulusWord input :: routeStack input }

/-- Zero-modulus branch boundary before its return tail. -/
def zeroState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 3563
    stack := modulusWord input :: routeStack input }

/-- Boundary after table slot `power` has been stored. -/
def tableState (input : ByteArray) (power pc : Nat) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat pc
    stack := [tableWord (baseWord input) (modulusWord input) power,
      baseWord input, modulusWord input] ++ routeStack input
    memory := tableMemoryThrough (baseWord input) (modulusWord input)
      (power + 1)
    activeWords := UInt256.ofNat (power + 1) }

/-- Loop head after the sixteen-entry table has been constructed. -/
def loopState (input : ByteArray) (pointer : Nat) (accumulator : UInt256) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 3197
    stack := [UInt256.ofNat pointer, accumulator, modulusWord input] ++
      routeStack input
    memory := tableMemory (baseWord input) (modulusWord input)
    activeWords := UInt256.ofNat 16 }

/-- Untaken loop guard boundary, immediately before loading the next calldata
word. -/
def loopContinueState (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) : State :=
  { loopState input pointer accumulator with pc := UInt256.ofNat 3206 }

/-- Accumulator after `count` of the four bytes in the currently loaded word.
The loop bytecode retains that word on the stack until all four bytes have
been consumed. -/
def byteAccumulator (input : ByteArray) (pointer : Nat) :
    Nat → UInt256 → UInt256
  | 0, accumulator => accumulator
  | count + 1, accumulator =>
      WindowMath.byteWordStep (modulusWord input) (baseWord input)
        (byteAccumulator input pointer count accumulator)
        (UInt256.byteAt (UInt256.ofNat count)
          (MachineState.readWord input pointer)).toNat

/-- Boundary before a byte segment (`count = 0`) or after one of its four
byte segments (`1 ≤ count ≤ 4`). -/
def wordState (input : ByteArray) (pointer count pc : Nat)
    (accumulator : UInt256) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat pc
    stack := [MachineState.readWord input pointer, UInt256.ofNat pointer,
      byteAccumulator input pointer count accumulator, modulusWord input] ++
        routeStack input
    memory := tableMemory (baseWord input) (modulusWord input)
    activeWords := UInt256.ofNat 16 }

theorem byteAccumulator_four (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) :
    byteAccumulator input pointer 4 accumulator =
      WindowMath.chunkWordStep (modulusWord input) (baseWord input) accumulator
        (MachineState.readWord input pointer) := by
  rfl

/-- Loop exit reached when the calldata pointer is 160. -/
def finishState (input : ByteArray) (accumulator : UInt256) : State :=
  { loopState input 160 accumulator with pc := UInt256.ofNat 3555 }

def outputMemory (word : UInt256) : ByteArray :=
  storeWord ByteArray.empty 0 word

def normalOutputMemory (input : ByteArray) (word : UInt256) : ByteArray :=
  storeWord (tableMemory (baseWord input) (modulusWord input)) 0 word

def returnedState (input : ByteArray) (word : UInt256) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 3563
    stack := modulusWord input :: routeStack input
    memory := normalOutputMemory input word
    activeWords := UInt256.ofNat 16
    halt := .Returned
    hReturn := MachineState.readPadded (normalOutputMemory input word) 0 32 }

def zeroReturnedState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 3570
    stack := modulusWord input :: routeStack input
    memory := outputMemory 0
    activeWords := UInt256.ofNat 1
    halt := .Returned
    hReturn := MachineState.readPadded (outputMemory 0) 0 32 }

/-! ## Segmented execution contracts

These aliases keep the concrete table-building proof split at stable bytecode
boundaries.  In particular, a table-slot proof never has to unfold either the
width guard or the complete fixed-width loop.
-/

abbrev ModulusNonzeroStep (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (WindowControlDefs.hitState input)
    (nonzeroState input)

abbrev ModulusZeroStep (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (WindowControlDefs.hitState input)
    (zeroState input)

abbrev TablePreludeStep (input : ByteArray) : Type :=
  Challenge.EvmProof.GasSteps (nonzeroState input)
    (tableState input 2 3053)

abbrev TableUpdateStep (input : ByteArray) (power nextPC : Nat) : Type :=
  Challenge.EvmProof.GasSteps (tableState input power nextPC)
    (tableState input (power + 1)
      (nextPC + if 32 * (power + 1) < 256 then 10 else 11))

abbrev LoopContinueStep (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) : Type :=
  Challenge.EvmProof.GasSteps (loopState input pointer accumulator)
    (wordState input pointer 0 3208 accumulator)

abbrev LoopExitStep (input : ByteArray) (accumulator : UInt256) : Type :=
  Challenge.EvmProof.GasSteps (loopState input 160 accumulator)
    (finishState input accumulator)

abbrev ByteStep (input : ByteArray) (pointer count startPC endPC : Nat)
    (accumulator : UInt256) : Type :=
  Challenge.EvmProof.GasSteps
    (wordState input pointer count startPC accumulator)
    (wordState input pointer (count + 1) endPC accumulator)

abbrev LoopAdvanceStep (input : ByteArray) (pointer : Nat)
    (accumulator : UInt256) : Type :=
  Challenge.EvmProof.GasSteps (wordState input pointer 4 3547 accumulator)
    (loopState input (pointer + 4)
      (WindowMath.chunkWordStep (modulusWord input) (baseWord input)
        accumulator (MachineState.readWord input pointer)))

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitStates
