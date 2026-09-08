import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectOutput

set_option warningAsError true

/-!
# Direct fixed-exponent boundary states

Artifact-independent state descriptions for the compact direct-output handler.
The concrete located paths live in `FixedDirectPaths` and its trace consumers.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates

open EvmSemantics
open EvmSemantics.EVM

abbrev outer := Exp.outer

def otherWidth (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3404
           stack := outer n bsize esize msize
           memory := mem }

def checkThree (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3413
           stack := outer n bsize esize msize
           memory := mem }

def check65537 (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3434
           stack := outer n bsize esize msize
           memory := mem }

def special (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3455
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def square (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3456
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def squareReturn (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3473
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def product (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3483
           stack := UInt256.ofNat 0 :: outer n bsize esize msize
           memory := mem }

def finish (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3500
           stack := outer n bsize esize msize
           memory := mem }

def fallback (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3505
           stack := outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
