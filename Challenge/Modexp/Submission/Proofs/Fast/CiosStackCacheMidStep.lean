import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMidStore
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMidProduct
import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheStates
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMidMemory

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

def midProgram : List Instr := CiosStackCachePrograms.midStore ++ CiosStackCachePrograms.midProduct

/-- The shorter cancellation sequence produces exactly the existing model's
multiplier and carry, after the two preceding memory stores. -/
theorem run_mid (s : State) (c : CachedMemory) (r : ReadOnlyCache) (carry bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 4 ≤ n) (hn32 : n ≤ 32) (hread : r.Valid c.virtual n)
    (htl : r.tl = UInt256.ofNat (8224+32*n))
    (hminv : (r.m0.toNat*r.inv.toNat+1)%2^256 = 0) :
    runInstructions midProgram (midAt s c r carry bi pa pb n i dst ret rest) =
    some (l2At 4953 s (cacheMid c carry) r bi (rowMu c.virtual n) (rowC0 c.virtual n)
      pa pb n i 0 dst ret rest) := by
  let d := cacheMid c carry
  have hro : r.Valid d.virtual n := hread.cacheMid r c carry n hn32
  have htlNat : r.tl.toNat = 8224+32*n := by
    rw [htl, Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have htlRead : MachineState.readWord d.memory r.tl.toNat =
      MachineState.readWord d.virtual (8224+32*n) := by
    rw [htlNat]
    exact (virtual_read_disjoint d _ (by omega)).symm
  have hmu : r.inv * MachineState.readWord d.memory r.tl.toNat = rowMu c.virtual n := by
    rw [htlRead, hro.inv]
    change rowMu d.virtual n = _
    rw [virtual_cacheMid, CiosCachedMidMemory.rowMu_mid _ _ _ (by omega)]
  have hc : UInt256.isZero (UInt256.isZero
      (r.m0*(r.inv*MachineState.readWord d.memory r.tl.toNat))) +
      mulHi r.m0 (r.inv*MachineState.readWord d.memory r.tl.toNat) = rowC0 c.virtual n := by
    rw [hmu, hread.m0]
    rfl
  have h1 := Mid.run_store s c r carry bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest hcap hact
  have h2 := Mid.run_words { s with memory := d.memory } (UInt256.ofNat 4935) d r bi
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest hcap
    (by rw [htlNat]; exact activeWords_fix s _ 32 (by decide) (by omega) hact) hminv
  rw [hc, hmu] at h2
  have hpc : advancePC 18 (UInt256.ofNat 4935) = UInt256.ofNat 4953 := by decide
  rw [hpc] at h2
  have hall := runInstructions_append_some _ _ _ _ _ h1 h2
  simpa only [midProgram, midAt, l2At, rowState, cacheL2, d] using hall

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_mid
