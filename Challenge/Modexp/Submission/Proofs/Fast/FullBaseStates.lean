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

/-- Persistent fast-path stack frame, top first. -/
def outer (n bsize esize msize : Nat) : List UInt256 :=
  [UInt256.ofNat (32 * n), UInt256.ofNat n, UInt256.ofNat bsize,
   UInt256.ofNat esize, UInt256.ofNat msize]

/-- The inherited base-chain head, a two-instruction redirect at pc1607. -/
def redirectState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1412
           stack := outer n bsize esize msize
           memory := memory }

/-- Redirected base-chain head, pc3146. -/
def entryState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2913
           stack := outer n bsize esize msize
           memory := memory }

/-- Guard hit, immediately before the calldata copy, pc3161. -/
def copyState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2928
           stack := outer n bsize esize msize
           memory := memory }

/-- RR-first Montgomery entry after copying the normal-domain base to ACC. -/
def addCallState (s : State) (memory input : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3924
           stack := [UInt256.ofNat 6144, UInt256.ofNat 1024,
             UInt256.ofNat 2048, UInt256.ofNat 1502] ++
             outer n bsize esize msize
           memory := copyBaseMem memory input n }

/-- Return from the conversion, immediately before inherited `bDone`. -/
def rejoinState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 1502
           stack := outer n bsize esize msize
           memory := memory }

/-- Guard miss, pc3184, with the original stack and memory. -/
def fallbackState (s : State) (memory : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 2951
           stack := outer n bsize esize msize
           memory := memory }

end Challenge.Modexp.Submission.Proofs.Fast.FullBase
