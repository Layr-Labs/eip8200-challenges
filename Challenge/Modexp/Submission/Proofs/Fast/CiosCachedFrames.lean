import Challenge.Modexp.Submission.Proofs.Fast.Monpro
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPrograms

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

def negative32 : UInt256 := UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639904
def allOnes : UInt256 := UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639935
def isFour (n : Nat) : UInt256 :=
  UInt256.eq (UInt256.ofNat 128) (UInt256.ofNat (32*n))

@[simp] theorem isFour_four : isFour 4 = UInt256.ofNat 1 := by decide
@[simp] theorem isFour_eight : isFour 8 = UInt256.ofNat 0 := by decide

def l1At (pc : Nat) (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (pa + 32 * n - 32) j),
                     UInt256.ofNat (ptrAt (8224 + 32 * n) j),
                     (l1Step mem bi pa n j).carry, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := (l1Step mem bi pa n j).memory }


def l2At (pc : Nat) (s : State) (mid : ByteArray) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat pc
           stack := [UInt256.ofNat (ptrAt (32 * n - 64) k),
                     UInt256.ofNat (ptrAt (8192 + 32 * n) k),
                     (l2Step mid mu c0 n k).carry, mu, bi,
                     UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa - 32), UInt256.ofNat (pb - 32), isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := (l2Step mid mu c0 n k).memory }


end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
