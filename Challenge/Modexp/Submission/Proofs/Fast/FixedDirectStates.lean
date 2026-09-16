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
  { s with pc := UInt256.ofNat 2405
           stack := outer n bsize esize msize
           memory := mem }

def checkThree (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2413
           stack := outer n bsize esize msize
           memory := mem }

def check65537 (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2433
           stack := outer n bsize esize msize
           memory := mem }

def special (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2453
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def square (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2453
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

def squareReturn (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2260
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- `after_sq` (pc 3360), reached two ways with the same shape: the in-kernel
square loop rewrites the kernel frame's return slot to it (the square count is
then still the one the caller pushed), and for the unaccelerated widths the
caller's own loop falls through to it with the count decremented to `0`. -/
def product (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 2269
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- **S1b.** Where every recogniser miss now goes: the bail trampoline at
pc 800.  The old miss target (2284 in the previous image) is an entry into
never-executed code that this artifact deletes, so it has no image under the pc
map and no mechanical pass may invent one -- `fixpcconst` reports it as
SKIPPED-deleted-no-image for exactly that reason.  800 is TRANSCRIBED from the
artifact's own `PUSH2` immediates at indices 2014 / 2023 / 2036. -/
def bailState (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 800
           stack := outer n bsize esize msize
           memory := mem }

/-- `modexpBig` at pc 238, where the trampoline lands.  `bigC_correct` re-reads
the header from calldata and is universal in the incoming memory and stack, so
the frame the fast path built is simply discarded. -/
def bigCState (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 238
           stack := outer n bsize esize msize
           memory := mem }

/-- **DEAD from S1b on.**  The generic fallback the recogniser used to rejoin.
Nothing reaches it: all three misses divert.  Kept, unreferenced by any located
proof, so that S2 retires it together with `FixedDirectFallbackCore` -- deleting
it here would remove the definition its own dead lemmas still mention. -/
def fallback (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2284
           stack := outer n bsize esize msize
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
