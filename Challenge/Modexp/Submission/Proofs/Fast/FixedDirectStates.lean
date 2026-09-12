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
  { s with pc := UInt256.ofNat 3019
           stack := outer n bsize esize msize
           memory := mem }

def checkThree (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3027
           stack := outer n bsize esize msize
           memory := mem }

def check65537 (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3047
           stack := outer n bsize esize msize
           memory := mem }

def special (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3067
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def square (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3067
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def squareReturn (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3088
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- `after_sq` (pc 3243), reached two ways with the same shape: the in-kernel
square loop rewrites the kernel frame's return slot to it (the square count is
then still the one the caller pushed), and for the unaccelerated widths the
caller's own loop falls through to it with the count decremented to `0`. -/
def product (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3098
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def fallback (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3114
           stack := outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
