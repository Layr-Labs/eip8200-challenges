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
  { s with pc := UInt256.ofNat 3343
           stack := outer n bsize esize msize
           memory := mem }

def checkThree (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3351
           stack := outer n bsize esize msize
           memory := mem }

def check65537 (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3371
           stack := outer n bsize esize msize
           memory := mem }

def special (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3391
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def square (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3392
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def squareReturn (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3409
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def product (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3419
           stack := UInt256.ofNat 0 :: outer n bsize esize msize
           memory := mem }

def finish (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3436
           stack := outer n bsize esize msize
           memory := mem }

def fallback (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3441
           stack := outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
