import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryCachePrefix

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

def cacheProgram : List Instr := entryProgram.take 32
def entryBodyProgram : List Instr := entryProgram.drop 32

theorem entryProgram_split : entryProgram = cacheProgram ++ entryBodyProgram := by
  exact (List.take_append_drop 32 entryProgram).symm

def cachedEntryState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4209
           stack := [UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, negative32, allOnes, l2Target n, modulusValue mem n, inverseValue mem, tailPointerValue mem, low64Value mem, low32Value mem, pdst, ret] ++ rest
           memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_cache (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1000) (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n))
    (hml : MachineState.readWord mem 9408 = modulusAddress n) :
    runInstructions cacheProgram (entryState s mem pa pb pdst ret rest) =
      some (cachedEntryState s mem pa pb n pdst ret rest) := by
  change runInstructions (CachePrefix.loadProgram ++ CachePrefix.shuffleProgram)
    (entryState s mem pa pb pdst ret rest) = _
  have hload := CachePrefix.run_load {s with memory := mem} (UInt256.ofNat pa) (UInt256.ofNat pb)
    pdst ret rest (32*n-32) hcap hact (by omega) hml
  have hshuffle := CachePrefix.run_shuffle {s with memory := mem} (UInt256.ofNat pa) (UInt256.ofNat pb)
    pdst ret (MachineState.readWord mem (32*n-32)) (inverseValue mem) (tailPointerValue mem) (low64Value mem) (low32Value mem) (CachePrefix.displacement mem) rest hcap
  have h := runInstructions_append_some _ _ _ _ _ hload hshuffle
  simpa only [entryState, cachedEntryState, l1Target, l2Target, modulusValue, inverseValue, tailPointerValue, low64Value, low32Value,
    CachePrefix.displacement, hs32, isFour] using h



end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
