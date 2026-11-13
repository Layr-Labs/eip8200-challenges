import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftStates
import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
noncomputable section
namespace CycleSubmission.Global.SlimFrames
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
-- The unchanged cached frame is the terminal base; no fields are reconstructed.
def outer (mem : ByteArray) (n bsize esize msize : Nat) : List UInt256 :=
 (CycleSubmission.Global.Fast.Shift.entrySlots (UInt256.ofNat 0) mem n bsize esize).tail.take 12 ++
  [CycleSubmission.Global.Fast.Shift.headWord mem n] ++ Challenge.Modexp.Submission.Proofs.Fast.Exp.outer n bsize esize msize
def frameState (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with pc := UInt256.ofNat pc, memory := mem, stack := outer mem n bsize esize msize}
def ridingFrame (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with pc := UInt256.ofNat pc, memory := mem, stack := UInt256.ofNat (32*n) :: outer mem n bsize esize msize}
def special (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
 {s with pc := UInt256.ofNat 3197, memory := mem, stack := [UInt256.ofNat (k-1), UInt256.ofNat (32*n)] ++ outer mem n bsize esize msize}
def guardFrame (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with pc := UInt256.ofNat pc, memory := mem, stack := [UInt256.ofNat 15,UInt256.ofNat (32*n)] ++ outer mem n bsize esize msize}
def bailState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State :=
 guardFrame s mem 207 n bsize esize msize
end CycleSubmission.Global.SlimFrames
