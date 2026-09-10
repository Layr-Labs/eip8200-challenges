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

def entryState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4160
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

def outState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4231
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, negative32, allOnes, l2Target n, modulusValue mem n, inverseValue mem, tailPointerValue mem, pdst, ret] ++ rest
           memory := mem }

/-- After the first loop: the carry and `b_i` above the row frame. -/
def midState (s : State) (mem : ByteArray) (c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4537
           stack := [c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, negative32, allOnes, l2Target n, modulusValue mem n, inverseValue mem, tailPointerValue mem, pdst, ret] ++ rest
           memory := mem }

/-- After the second loop: the carry, `mu` and `b_i` above the row frame. -/
def tailState (s : State) (mem : ByteArray) (c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4830
           stack := [c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat pa, UInt256.ofNat (pb - 32), l1Target n, negative32, allOnes, l2Target n, modulusValue mem n, inverseValue mem, tailPointerValue mem, pdst, ret] ++ rest
           memory := mem }

theorem negative32_not : UInt256.lnot (UInt256.ofNat 31) = negative32 := by decide
theorem allOnes_not : UInt256.lnot (UInt256.ofNat 0) = allOnes := by decide

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
