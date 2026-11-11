import Challenge.Modexp.Submission.Proofs.Fast.FixedDirectStates
noncomputable section
namespace CycleSubmission.Global.SlimFrames
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs
-- The two runtime fields read by the terminal caller; other sizes are ghost parameters.
def outer (n _bsize _esize _msize : Nat) : List UInt256 := [UInt256.ofNat (32*n)]
def frameState (s : State) (mem : ByteArray) (pc n bsize esize msize : Nat) : State :=
 {s with pc := UInt256.ofNat pc, memory := mem, stack := outer n bsize esize msize}
def special (s : State) (mem : ByteArray) (n bsize esize msize k : Nat) : State :=
 {s with pc := UInt256.ofNat 2336, memory := mem, stack := UInt256.ofNat (k-1) :: outer n bsize esize msize}
def bailState (s : State) (mem : ByteArray) (n bsize esize msize : Nat) : State := frameState s mem 207 n bsize esize msize
end CycleSubmission.Global.SlimFrames
