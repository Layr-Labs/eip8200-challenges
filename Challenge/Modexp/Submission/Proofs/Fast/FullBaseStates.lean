import Challenge.Modexp.Submission.Proofs.Fast.FullBaseLogic
set_option warningAsError true
/-!
# Boundary states for the full-width-base helper

The definitions here are intentionally independent of `Fast.Exp`. This lets
the driver import the helper without creating an import cycle; its existing
`outer`, `amCall`, and `mpCall` states are definitionally equal to the shapes
below at the corresponding boundaries.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FullBase

open EvmSemantics
open EvmSemantics.EVM

def outer (n bsize esize msize : Nat) : List UInt256 :=
  [UInt256.ofNat (32 * n), UInt256.ofNat n, UInt256.ofNat bsize,
   UInt256.ofNat esize, UInt256.ofNat msize]

def redirectState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 850
           stack := outer n bsize esize msize
           memory := memory }

def entryState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2483
           stack := outer n bsize esize msize
           memory := memory }

def copyState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2497
           stack := outer n bsize esize msize
           memory := memory }

def addCallState (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3406
           stack := [UInt256.ofNat 1536, UInt256.ofNat 256,
             UInt256.ofNat 512, UInt256.ofNat 2492] ++
             outer n bsize esize msize
           memory := copyBaseMem memory input n }

def rejoinState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2492
           stack := outer n bsize esize msize
           memory := memory }

def fallbackState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1802
           stack := outer n bsize esize msize
           memory := memory }

end Challenge.Modexp.Submission.Proofs.Fast.FullBase
