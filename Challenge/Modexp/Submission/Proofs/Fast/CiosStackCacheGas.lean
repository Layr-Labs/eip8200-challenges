import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheBlockInterface

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

variable {art : ProgramArtifact}

opaque l1Step (pc : Nat) (s : State) (env : Environment art .Osaka s)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (block : Block art .Osaka pc (l1StepFor (n-1-j)))
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hj : j < n) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) :
    GasSteps (l1At pc s c r bi pa pb n i j dst ret rest)
      (l1At (pc+l1BodySize (n-1-j)+2) s c r bi pa pb n i (j+1) dst ret rest) :=
  block.steps (env.transfer rfl rfl) rfl
    (run_l1Step pc s c r bi pa pb n i j dst ret rest hcap hact hn hj hpa hfit)

opaque l1Last (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hpos : 0 < n) (hpa : 32 ≤ pa) (hfit : pa+32*n ≤ 8192) :
    GasSteps (l1At 4510 s c r bi pa pb n i (n-1) dst ret rest)
      (midAt s (cacheL1 c bi pa n n).cache r (cacheL1 c bi pa n n).carry bi
        pa pb n i dst ret rest) :=
  blocks.l1Mac7.steps (env.transfer rfl rfl) rfl
    (run_l1Last s c r bi pa pb n i dst ret rest hcap hact hn hpos hpa hfit)

opaque l2Step (pc : Nat) (s : State) (env : Environment art .Osaka s)
    (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb n i k : Nat) (dst ret : UInt256) (rest : List UInt256)
    (block : Block art .Osaka pc (l2BodyFor (n-2-k)))
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : n ≤ 32) (hk : k+1 < n) (hread : r.Valid c.virtual n) :
    GasSteps (l2At pc s c r bi mu c0 pa pb n i k dst ret rest)
      (l2At (pc+l2BodySize (n-2-k)) s c r bi mu c0 pa pb n i (k+1) dst ret rest) :=
  block.steps (env.transfer rfl rfl) rfl
    (run_l2Step pc s c r bi mu c0 pa pb n i k dst ret rest hcap hact hn hk hread)

opaque out (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 8192) (hi : i < n) :
    GasSteps (outAt s c r pa pb n i dst ret rest)
      (l1At 4248 s c r (rowBi c.virtual pb n i) pa pb n i 0 dst ret rest) :=
  blocks.out.steps (env.transfer rfl rfl) rfl
    (run_out s c r pa pb n i dst ret rest hcap hact hpb hfit hi)

opaque mid (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (carry bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hn : 4 ≤ n) (hn32 : n ≤ 32) (hread : r.Valid c.virtual n)
    (htl : r.tl = UInt256.ofNat (8224+32*n))
    (hminv : (r.m0.toNat*r.inv.toNat+1)%2^256 = 0) :
    GasSteps (midAt s c r carry bi pa pb n i dst ret rest)
      (l2At 4576 s (cacheMid c carry) r bi (rowMu c.virtual n) (rowC0 c.virtual n)
        pa pb n i 0 dst ret rest) :=
  blocks.mid.steps (env.transfer rfl rfl) rfl
    (run_mid s c r carry bi pa pb n i dst ret rest hcap hact hn hn32 hread htl hminv)

opaque tail (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (carry mu bi : UInt256)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpb : 32 ≤ pb) (hfit : pb+32*n ≤ 8192) (hi : i+1 ≤ n) :
    GasSteps (tailAt s c r carry mu bi pa pb n i dst ret rest)
      (rowState s (if i+1 < n then 4243 else 4855) (CiosStackCacheModel.cacheTail c carry)
        r pa pb n (i+1) dst ret rest []) :=
  blocks.tail.steps (env.transfer rfl rfl) rfl
    (run_tail s c r carry mu bi pa pb n i dst ret rest hcap hact hpb hfit hi
      (by rw [env.code]; exact blocks.jumpOut))

opaque exit (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache)
    (pa pb n i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    GasSteps (rowState s 4855 c r pa pb n i dst ret rest [])
      (mpCsubState s c.virtual dst ret rest) :=
  blocks.exit.steps (env.transfer rfl rfl) rfl
    (run_exit s c r pa pb n i dst ret rest hcap hact (by rw [env.code]; exact blocks.jumpCsub))


opaque l1Dispatch (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    GasSteps (l1At 4248 s c r bi pa pb n i j dst ret rest)
      (l1At (if UInt256.isTrue (CiosCached.isFour n) then 4405 else 4253)
        s c r bi pa pb n i j dst ret rest) := by
  let p := cacheL1 c bi pa n j
  refine blocks.l1Dispatch.steps (s := l1At 4248 s c r bi pa pb n i j dst ret rest) (env.transfer rfl rfl) rfl ?_
  have h := run_dispatch { s with memory := p.cache.memory } 4248 4405 p.cache r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret (UInt256.ofNat (ptrAt (pa+32*n-32) j)) p.carry bi rest hcap
    (by decide) (by rw [env.code]; exact blocks.jumpL1)
  simpa only [l1At, rowState, p] using h

opaque l1Join (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    GasSteps (l1At 4405 s c r bi pa pb n i j dst ret rest)
      (l1At 4406 s c r bi pa pb n i j dst ret rest) := by
  let p := cacheL1 c bi pa n j
  refine blocks.l1Join.steps (s := l1At 4405 s c r bi pa pb n i j dst ret rest) (env.transfer rfl rfl) rfl ?_
  have h := run_join { s with memory := p.cache.memory } 4405
    ([UInt256.ofNat (ptrAt (pa+32*n-32) j), p.carry, bi] ++ rowFrame p.cache r
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
      (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest)
    (by simp only [rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]; omega)
  simpa only [l1At, rowState, p] using h

opaque l2Dispatch (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    GasSteps (l2At 4576 s c r bi mu c0 pa pb n i j dst ret rest)
      (l2At (if UInt256.isTrue (CiosCached.isFour n) then 4729 else 4581)
        s c r bi mu c0 pa pb n i j dst ret rest) := by
  let p := cacheL2 c mu c0 n j
  refine blocks.l2Dispatch.steps (s := l2At 4576 s c r bi mu c0 pa pb n i j dst ret rest) (env.transfer rfl rfl) rfl ?_
  have h := run_dispatch { s with memory := p.cache.memory } 4576 4729 p.cache r
    (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
    (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret p.carry mu bi rest hcap
    (by decide) (by rw [env.code]; exact blocks.jumpL2)
  simpa only [l2At, rowState, p] using h

opaque l2Join (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb n i j : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) :
    GasSteps (l2At 4729 s c r bi mu c0 pa pb n i j dst ret rest)
      (l2At 4730 s c r bi mu c0 pa pb n i j dst ret rest) := by
  let p := cacheL2 c mu c0 n j
  refine blocks.l2Join.steps (s := l2At 4729 s c r bi mu c0 pa pb n i j dst ret rest) (env.transfer rfl rfl) rfl ?_
  have h := run_join { s with memory := p.cache.memory } 4729
    ([p.carry, mu, bi] ++ rowFrame p.cache r
      (UInt256.ofNat (ptrAt (pb+32*n-32) i)) (UInt256.ofNat (pa+32*n-32))
      (UInt256.ofNat (pb-32)) (CiosCached.isFour n) dst ret rest)
    (by simp only [rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]; omega)
  simpa only [l2At, rowState, p] using h

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas
