import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
import Challenge.Modexp.Submission.Proofs.Fast.FixedExponentLogic

set_option warningAsError true

/-!
# Fixed-exponent dispatcher boundary states

These states describe only stack, memory, and program-counter boundaries.
They are independent of the concrete `ProgramArtifact`, allowing the located
trace modules to remain small and separately rebuildable after byte changes.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates

open EvmSemantics
open EvmSemantics.EVM

abbrev outer := Exp.outer

/-- Fallthrough after the three-byte width test, before testing width one. -/
def otherWidth (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3687
           stack := outer n bsize esize msize
           memory := mem }

/-- One-byte exponent calldata check. -/
def checkThree (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3696
           stack := outer n bsize esize msize
           memory := mem }

/-- Three-byte exponent calldata check. -/
def check65537 (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3717
           stack := outer n bsize esize msize
           memory := mem }

/-- Entry shared by the two fixed addition chains. -/
def special (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3738
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- Squaring call site after the initial BASE-to-ACC copy. -/
def square (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3764
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- Return from one Montgomery square. -/
def squareReturn (s : State) (mem : ByteArray)
    (n bsize esize msize count : Nat) : State :=
  { s with pc := UInt256.ofNat 3781
           stack := UInt256.ofNat count :: outer n bsize esize msize
           memory := mem }

/-- Counter-zero fallthrough to the final multiply by BASE. -/
def product (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3791
           stack := UInt256.ofNat 0 :: outer n bsize esize msize
           memory := mem }

/-- Return from the final Montgomery product. -/
def decode (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3791
           stack := outer n bsize esize msize
           memory := mem }

/-- Return from Montgomery decoding, immediately before the inherited return. -/
def finish (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3833
           stack := outer n bsize esize msize
           memory := mem }

/-- Shared generic fallback before copying R1 to ACC. -/
def fallback (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { s with pc := UInt256.ofNat 3821
           stack := outer n bsize esize msize
           memory := mem }

/-- Memory at the first square call. -/
def initialSquareMem (mem : ByteArray) (n : Nat) : ByteArray :=
  Exp.mcopyMem mem 1024 2048 (32 * n)

theorem initialSquareMem_eq (mem : ByteArray) (n : Nat) :
    initialSquareMem mem n =
      FixedExponentLogic.fixedMems (fun _ _ _ m => m) n mem 0 := by
  rfl

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentStates
