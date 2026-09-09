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
  { s with pc := UInt256.ofNat 4481
           stack := [UInt256.ofNat pa, UInt256.ofNat pb, pdst, ret] ++ rest
           memory := mem }

def outState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4595
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa + 32*n - 32), UInt256.ofNat (pb - 32), isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := mem }


def midState (s : State) (mem : ByteArray) (paj ptj c bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4902
           stack := [paj, ptj, c, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa + 32*n - 32), UInt256.ofNat (pb - 32), isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := mem }


def tailState (s : State) (mem : ByteArray) (pmj ptj c mu bi : UInt256)
    (pa pb n i : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 5262
           stack := [pmj, ptj, c, mu, bi, UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa + 32*n - 32), UInt256.ofNat (pb - 32), isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := mem }


theorem negative32_not : UInt256.lnot (UInt256.ofNat 31) = negative32 := by decide
theorem allOnes_not : UInt256.lnot (UInt256.ofNat 0) = allOnes := by decide

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
