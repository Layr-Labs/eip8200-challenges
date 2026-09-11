import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

/-- Virtual leading JUMPDEST for composing the uncached entry template. -/
def maskEntryState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { entryState s mem pa pb pdst ret rest with pc := UInt256.ofNat 4107 }

def cacheProgram : List Instr := entryProgram.take 18
def entryBodyProgram : List Instr := entryProgram.drop 18

theorem entryProgram_split : entryProgram = cacheProgram ++ entryBodyProgram := by
  exact (List.take_append_drop 18 entryProgram).symm

def cachedEntryState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4227
           stack := [UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
