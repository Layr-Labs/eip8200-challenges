import Challenge.Modexp.Submission.Proofs.Bytecode.WindowFinalByte

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleForward

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowByteKernel

/-- Keep the newly computed product on top; the old accumulator is discarded
only after the following low-nibble lookup. The nibble is a compatibility label. -/
def forwardedNibbleState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer original accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := nibbleState template pc base modulus nibble byte word pointer original rest
  { state with stack := [accumulator, byte, word, pointer, original, modulus] ++ rest }

/-- The last byte has already consumed the calldata word. -/
def finalForwardedNibbleState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer original accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := nibbleState template pc base modulus nibble byte word pointer original rest
  { state with stack := [accumulator, byte, pointer, original, modulus] ++ rest }

def forwardHighLookupProgram : List Instr :=
  [.op (.Dup ⟨6, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 17 5, .op .SHL, .op .MLOAD, .op .MULMOD]

def forwardHighSquareLookupProgram : List Instr :=
  fourSquareProgram ++ forwardHighLookupProgram

def forwardFinalHighLookupProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 17 5, .op .SHL, .op .MLOAD, .op .MULMOD]

def forwardFinalHighSquareLookupProgram : List Instr :=
  lowFourSquareProgram ++ forwardFinalHighLookupProgram

/-- Four moduli are staged below the forwarded accumulator, consuming its
top stack slot instead of duplicating an older accumulator below the frame. -/
def forwardLowSquareProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def forwardFinalLowSquareProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .op (.Swap ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def forwardLowLookupProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 1 15, .op .AND, .push 17 5, .op .SHL, .op .MLOAD,
   .op .MULMOD, .op (.Swap ⟨2, by decide⟩), .op .POP]

def forwardFinalLowLookupProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 1 15, .op .AND, .push 19 5, .op .SHL, .op .MLOAD,
   .op .MULMOD, .op (.Swap ⟨1, by decide⟩), .op .POP]

def forwardLowSquareLookupProgram : List Instr :=
  forwardLowSquareProgram ++ forwardLowLookupProgram

def forwardFinalLowSquareLookupProgram : List Instr :=
  forwardFinalLowSquareProgram ++ forwardFinalLowLookupProgram

def forwardLowPrepProgram : List Instr := []

def forwardByteProgram (index : Nat) : List Instr :=
  highPrepProgram index ++ forwardHighSquareLookupProgram ++
    forwardLowPrepProgram ++ forwardLowSquareLookupProgram ++ finishProgram

def forwardFinalByteProgram : List Instr :=
  finalHighPrepProgram ++ forwardFinalHighSquareLookupProgram ++
    forwardLowPrepProgram ++ forwardFinalLowSquareLookupProgram ++ finishProgram

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleForward
