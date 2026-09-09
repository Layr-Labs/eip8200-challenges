import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheSchedules

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 600000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInit

variable {art : ProgramArtifact}

opaque l1Width (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) :
    GasSteps (l1At 4600 s c r bi pa pb n i 0 dst ret rest)
      (midAt s (cacheL1 c bi pa n n).cache r (cacheL1 c bi pa n n).carry bi
        pa pb n i dst ret rest) := by
  by_cases h4 : n = 4
  · subst n; exact l1Four s env blocks c r bi pa pb i dst ret rest hcap hact hpa hfit
  · have h8 := hw.resolve_left h4
    subst n; exact l1Eight s env blocks c r bi pa pb i dst ret rest hcap hact hpa hfit

opaque l2Width (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8) (hread : r.Valid c.virtual n) :
    GasSteps (l2At 4928 s c r bi mu c0 pa pb n i 0 dst ret rest)
      (tailAt s (cacheL2 c mu c0 n (n-1)).cache r (cacheL2 c mu c0 n (n-1)).carry mu bi
        pa pb n i dst ret rest) := by
  by_cases h4 : n = 4
  · subst n; exact l2Four s env blocks c r bi mu c0 pa pb i dst ret rest hcap hact hread
  · have h8 := hw.resolve_left h4
    subst n; exact l2Eight s env blocks c r bi mu c0 pa pb i dst ret rest hcap hact hread

/-- One complete row up to the final carry stores and outer-loop test. -/
opaque rowToTail (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 8192)
    (hread : r.Valid c.virtual n) (htl : r.tl = UInt256.ofNat (8224+32*n))
    (hminv : (r.m0.toNat*r.inv.toNat+1)%2^256 = 0) :
    GasSteps (outAt s c r pa pb n i dst ret rest)
      (tailAt s (cacheRowL2 c pa pb n i).cache r (cacheRowL2 c pa pb n i).carry
        (rowMu (cacheRowL1 c pa pb n i).cache.virtual n) (rowBi c.virtual pb n i)
        pa pb n i dst ret rest) := by
  have hn32 : n ≤ 32 := by omega
  have hr1 := hread.cacheL1 r c (rowBi c.virtual pb n i) pa n n hn32
  have hr2 := hr1.cacheMid r (cacheRowL1 c pa pb n i).cache
    (cacheRowL1 c pa pb n i).carry n hn32
  refine (out s env blocks c r pa pb n i dst ret rest hcap hact hpb hpbFit hi).trans ?_
  refine (l1Width s env blocks c r (rowBi c.virtual pb n i) pa pb n i dst ret rest
    hcap hact hw hpa hpaFit).trans ?_
  refine (mid s env blocks (cacheRowL1 c pa pb n i).cache r
    (cacheRowL1 c pa pb n i).carry (rowBi c.virtual pb n i) pa pb n i dst ret rest
    hcap hact (by omega) hn32 hr1 htl hminv).trans ?_
  exact l2Width s env blocks (cacheRowMid c pa pb n i) r (rowBi c.virtual pb n i)
    (rowMu (cacheRowL1 c pa pb n i).cache.virtual n)
    (rowC0 (cacheRowL1 c pa pb n i).cache.virtual n) pa pb n i dst ret rest hcap hact hw hr2

opaque rowNext (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8) (hi : i+1 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 8192)
    (hread : r.Valid c.virtual n) (htl : r.tl = UInt256.ofNat (8224+32*n))
    (hminv : (r.m0.toNat*r.inv.toNat+1)%2^256 = 0) :
    GasSteps (outAt s c r pa pb n i dst ret rest)
      (outAt s (cacheRow c pa pb n i) r pa pb n (i+1) dst ret rest) := by
  refine (rowToTail s env blocks c r pa pb n i dst ret rest hcap hact hw (by omega)
    hpa hpaFit hpb hpbFit hread htl hminv).trans ?_
  have h := tail s env blocks (cacheRowL2 c pa pb n i).cache r (cacheRowL2 c pa pb n i).carry
    (rowMu (cacheRowL1 c pa pb n i).cache.virtual n) (rowBi c.virtual pb n i)
    pa pb n i dst ret rest hcap hact hpb hpbFit (by omega)
  simpa only [if_pos hi, outAt, cacheRow] using h

opaque rowLast (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8) (hi : i+1 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 8192)
    (hread : r.Valid c.virtual n) (htl : r.tl = UInt256.ofNat (8224+32*n))
    (hminv : (r.m0.toNat*r.inv.toNat+1)%2^256 = 0) :
    GasSteps (outAt s c r pa pb n i dst ret rest)
      (mpCsubState s (cacheRow c pa pb n i).virtual dst ret rest) := by
  refine (rowToTail s env blocks c r pa pb n i dst ret rest hcap hact hw (by omega)
    hpa hpaFit hpb hpbFit hread htl hminv).trans ?_
  have h := tail s env blocks (cacheRowL2 c pa pb n i).cache r (cacheRowL2 c pa pb n i).carry
    (rowMu (cacheRowL1 c pa pb n i).cache.virtual n) (rowBi c.virtual pb n i)
    pa pb n i dst ret rest hcap hact hpb hpbFit (by omega)
  have hstop : ¬i+1 < n := by omega
  simp only [if_neg hstop] at h
  exact h.trans (exit s env blocks (cacheRow c pa pb n i) r pa pb n (i+1) dst ret rest hcap hact)

/-- The complete outer loop, including the final cache flush. -/
opaque rows (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hw : n = 4 ∨ n = 8)
    (hpa : 32 ≤ pa) (hpaFit : pa+32*n ≤ 8192)
    (hpb : 32 ≤ pb) (hpbFit : pb+32*n ≤ 8192)
    (hread : r.Valid c.virtual n) (htl : r.tl = UInt256.ofNat (8224+32*n))
    (hminv : (r.m0.toNat*r.inv.toNat+1)%2^256 = 0) :
    GasSteps (outAt s c r pa pb n 0 dst ret rest)
      (mpCsubState s (cacheRows c pa pb n n).virtual dst ret rest) := by
  refine (GasSteps.iterateBounded
    (I := fun i => outAt s (cacheRows c pa pb n i) r pa pb n i dst ret rest)
    (n-1) ?_).trans ?_
  · intro i hi
    exact rowNext s env blocks (cacheRows c pa pb n i) r pa pb n i dst ret rest
      hcap hact hw (by omega) hpa hpaFit hpb hpbFit
      (hread.cacheRows r c pa pb n i (by omega)) htl hminv
  · have hn : n-1+1 = n := by omega
    have h := rowLast s env blocks (cacheRows c pa pb n (n-1)) r pa pb n (n-1) dst ret rest
      hcap hact hw hn hpa hpaFit hpb hpbFit
      (hread.cacheRows r c pa pb n (n-1) (by omega)) htl hminv
    have hc : cacheRow (cacheRows c pa pb n (n-1)) pa pb n (n-1) = cacheRows c pa pb n n := by
      rw [← hn]
      rfl
    simpa only [hc] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas.rows
