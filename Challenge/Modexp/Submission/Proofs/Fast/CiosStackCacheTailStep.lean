import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheTail
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheExit
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheStates
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedPointers

set_option warningAsError true
set_option maxRecDepth 2048
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

def tailProgram : List Instr :=
  (CiosStackCachePrograms.tailCleanup ++ CiosStackCachePrograms.tailStore) ++ CiosStackCachePrograms.tailTest

theorem run_tail (s : State) (c : CachedMemory) (r : ReadOnlyCache) (carry mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 8192) (hi : i+1 ≤ n)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 4595 = true) :
    runInstructions tailProgram (tailAt s c r carry mu bi pa pb n i dst ret rest) =
    some (rowState s (if i+1 < n then 4595 else 5212) (CiosStackCacheModel.cacheTail c carry)
      r pa pb n (i+1) dst ret rest []) := by
  let d := CiosStackCacheModel.cacheTail c carry
  have h1 := Tail.run_cleanup { s with memory := c.memory } c r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret carry mu bi rest hcap
  have h2 := Tail.run_store s c r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret carry rest hcap hact
  have h3 := Tail.run_test { s with memory := d.memory } d r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest hcap hjump
  rw [cursor_next] at h3
  have hcond : UInt256.isTrue
      (UInt256.gt (UInt256.ofNat (ptrAt (pb+32*n-32) (i+1))) (UInt256.ofNat (pb-32))) ↔ i+1 < n :=
    CiosCachedPointers.l1_condition pb n (i+1) hpb (by omega) hi
  simp only [hcond] at h3
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have hall := runInstructions_append_some _ _ _ _ _ h12 h3
  by_cases hnext : i+1 < n
  · simpa only [tailProgram, tailAt, rowState, d, if_pos hnext] using hall
  · simpa only [tailProgram, tailAt, rowState, d, if_neg hnext] using hall

theorem run_exit (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hjump : Decode.isValidJumpDest s.executionEnv.code 2304 = true) :
    runInstructions CiosStackCachePrograms.exit (rowState s 5212 c r pa pb n i dst ret rest []) =
    some (mpCsubState s c.virtual dst ret rest) := by
  simpa only [rowState, mpCsubState, framed, List.nil_append] using Exit.run_exit s c r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest hcap hact hjump

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_tail
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_exit
