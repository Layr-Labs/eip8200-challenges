import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheKernel
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheEntry
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheExit
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheProgramChecks
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMidProduct
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMidStore
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheTail

set_option warningAsError true

/-!
Audit for the 663659-gas stack-cache kernel. Concrete row traces, both fixed
width schedules, the complete outer loop and initialization/flush now compose
into Gas.kernel, parameterized by exact block certificates. CiosStackCacheBlocks
instantiates those certificates against the submitted Artifact; CiosStackCacheFull
connects the kernel to the universal MODEXP proof used by Solution.
-/
namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheProofAudit

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

/-- The initialized cache model exactly reproduces the accepted memory
recursion after any number of CIOS rows. The separate instruction certificates
supply the per-block EVM behavior used to implement this model. -/
theorem flushed_rows_same (s : State) (mem : ByteArray) (pa pb n i : Nat) (hn : 3 ≤ n) :
    (cacheRows (initial s mem n) pa pb n i).virtual =
      rowsMem (mpZeroed s mem n) pa pb n i := by
  rw [virtual_cacheRows, virtual_initial s mem n hn]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheProofAudit

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheProofAudit.flushed_rows_same
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Entry.run_entry
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_cachedL1Body
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_cachedL2Body
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_partialL2Body
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Mid.run_store
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Mid.run_words
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Tail.run_store
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Tail.run_test
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Exit.run_exit
#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas.kernel
