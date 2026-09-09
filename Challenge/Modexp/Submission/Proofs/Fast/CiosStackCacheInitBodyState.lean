import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryDefs

set_option warningAsError true
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

def zeroProgram : List Instr := (entryProgram.drop 11).take 8
def pointersProgram : List Instr := entryProgram.drop 19

theorem entryBody_split : entryBodyProgram = zeroProgram ++ pointersProgram := rfl

def clearedState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4573
           stack := [UInt256.ofNat (32*n), UInt256.ofNat pa, UInt256.ofNat pb,
             isFour n, negative32, allOnes, dst, ret] ++ rest
           memory := mpZeroed s mem n }

def cachedEntryState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4560
           stack := [UInt256.ofNat pa, UInt256.ofNat pb,
             isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := mem }


def outState (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4595
           stack := [UInt256.ofNat (ptrAt (pb + 32 * n - 32) i),
                     UInt256.ofNat (pa + 32*n - 32), UInt256.ofNat (pb - 32), isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := mem }


end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody
