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
  { s with pc := UInt256.ofNat 2450
           stack := outer n bsize esize msize
           memory := mem }

def checkThree (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2458
           stack := outer n bsize esize msize
           memory := mem }

def check65537 (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2478
           stack := outer n bsize esize msize
           memory := mem }

def special (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2498
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def square (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2498
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def squareReturn (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2519
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- `after_sq` (pc 3367), reached two ways with the same shape: the in-kernel
square loop rewrites the kernel frame's return slot to it (the square count is
then still the one the caller pushed), and for the unaccelerated widths the
caller's own loop falls through to it with the count decremented to `0`. -/
def product (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2528
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- Where every recogniser miss now goes: the six-word bail trampoline `BAIL6` at
pc 1054.  All three checks (`esize = 1`, first byte `3`, top three bytes `65537`)
`JUMPI` here instead of copying `R1` to `ACC` and rejoining the generic loop. -/
def bailState (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 790
           stack := outer n bsize esize msize
           memory := mem }

/-- `modexpBig` at pc 237, where the trampoline lands.  The wide-modulus fallback
re-reads the header from calldata and is universal in the incoming memory and
stack, so the frame the fast path built is simply discarded. -/
def bigCState (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 238
           stack := outer n bsize esize msize
           memory := mem }

/-- The generic rejoin the recogniser used to take.  Nothing reaches it any more:
all three misses divert to `bailState`. -/
def fallback (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2543
           stack := outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
