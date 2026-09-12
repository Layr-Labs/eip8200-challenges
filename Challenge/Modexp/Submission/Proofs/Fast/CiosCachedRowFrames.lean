import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

/-- Kernel `setup` entry (pc 3948, 0x0f6c), reached from `common` with the row head
`hd` above the call frame. -/
def setupState (s : State) (mem : ByteArray) (hd : UInt256) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3923
           stack := [hd, UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

/-- Row head `i`: the program counter is the frame's own row head `hd`. -/
def outState (s : State) (mem : ByteArray) (pb n i : Nat)
    (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := hd
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

/-- After the first loop, at the middle block's `JUMPDEST` (pc 4334): the carry and
`b_i` above the row frame. -/
def midState (s : State) (mem : ByteArray) (c bi : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4309
           stack := [c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

/-- After the second loop: the carry, `mu` and `b_i` above the row frame. -/
def tailState (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pb n i : Nat) (hd ent pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4598
           stack := [c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     hd, UInt256.ofNat (pb - 32), ent, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

theorem negative32_not : UInt256.lnot (UInt256.ofNat 31) = negative32 := by decide
theorem allOnes_not : UInt256.lnot (UInt256.ofNat 0) = allOnes := by decide

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
