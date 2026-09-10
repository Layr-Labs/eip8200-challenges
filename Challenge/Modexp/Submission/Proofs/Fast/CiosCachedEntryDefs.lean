import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryCache

set_option warningAsError true
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def zeroProgram : List Instr := (entryProgram.drop 18).take 8
def pointersProgram : List Instr := entryProgram.drop 26

theorem entryBody_split : entryBodyProgram = zeroProgram ++ pointersProgram := rfl

def clearedState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4236
           stack := [UInt256.ofNat (32*n), UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, negative32, allOnes, l2Target n, dst, ret] ++ rest
           memory := mpZeroed s mem n }

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
