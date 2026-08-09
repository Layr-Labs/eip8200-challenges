import Challenge.Sha256.Submission.Proofs.Bytecode.PaddingTrace

set_option warningAsError true
set_option maxRecDepth 10000

/-!
# Semantic states for eliminated SHA-256 memory accessors

The optimized artifact has no live calls to the compiler-generated accessor
bodies.  Their executable bytes are therefore used as unreachable structural
padding.  The semantic state constructors remain useful to the higher-level
proofs: direct `MLOAD` and `MSTORE` paths deliberately terminate in the same
states that the old accessor calls returned.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.Accessors

open EvmSemantics
open EvmSemantics.EVM

def slotOffset (base : Nat) (index : UInt256) : Nat :=
  (UInt256.shiftLeft index (UInt256.ofNat 5) + UInt256.ofNat base).toNat

def loadEntry (s : State) (entry : Nat) (index output returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entry
    stack := [index, output, returnDest] ++ rest }

def loadReturned (s : State) (base : Nat) (index returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := MachineState.readWord s.memory (slotOffset base index) :: rest
    activeWords := s.activeWordsAfterUInt256 (slotOffset base index) 32 }

def storeEntry (s : State) (entry : Nat) (index value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat entry
    stack := [index, value, returnDest] ++ rest }

def storeReturned (s : State) (base : Nat) (index value returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := returnDest
    stack := rest
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (slotOffset base index)
    activeWords := s.activeWordsAfterUInt256 (slotOffset base index) 32 }

def kAtReturned (s : State) (index returnDest : UInt256)
    (rest : List UInt256) : State :=
  let offset :=
    (UInt256.shiftLeft index (UInt256.ofNat 2) + UInt256.ofNat 32).toNat
  { s with
    pc := returnDest
    stack := UInt256.shiftRight (MachineState.readWord s.memory offset)
      (UInt256.ofNat 224) :: rest
    activeWords := s.activeWordsAfterUInt256 offset 32 }

end Challenge.Sha256.Submission.Proofs.Bytecode.Accessors
