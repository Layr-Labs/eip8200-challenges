import Challenge.Modexp.Submission.Proofs.Fast.SquareLoopMem

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

/-- The kernel setup used to store a zero word at `0x0800` (2048).  Every route overwrites that
word before reading it (the square rows go through `Monpro.mpZeroed`, the other kernels write the
row before they load it), so the store is gone and this is the identity. -/
def memory (mem : ByteArray) : ByteArray := mem

theorem readWord_outside (mem : ByteArray) (addr : Nat)
    (_hout : addr + 32 ≤ 2048 ∨ 2080 ≤ addr) :
    MachineState.readWord (memory mem) addr = MachineState.readWord mem addr := rfl

theorem fastRepresents_outside (mem : ByteArray) (ptr n value : Nat)
    (_hout : ptr + 32*n ≤ 2048 ∨ 2080 ≤ ptr)
    (hrep : Model.FastRepresents mem ptr n value) :
    Model.FastRepresents (memory mem) ptr n value := hrep

theorem mpZeroed_eq (s : State) (mem : ByteArray) (n : Nat) :
    Monpro.mpZeroed s (memory mem) n = Monpro.mpZeroed s mem n := rfl

theorem sqRound_eq (s : State) (n c : Nat) (mem : ByteArray) :
    SquareLoopMem.sqRound s n c (memory mem) =
      SquareLoopMem.sqRound s n c mem := rfl

theorem sqRunMem_eq (s : State) (n k : Nat) (mem : ByteArray) (_hk : 1 ≤ k) :
    SquareLoopMem.sqRunMem s n k (memory mem) =
      SquareLoopMem.sqRunMem s n k mem := rfl

end Challenge.Modexp.Submission.Proofs.Fast.SquarePartialClear
