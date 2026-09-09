import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheGas

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode WindowTwentyOneBinding
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

variable {art : ProgramArtifact}

opaque l1Four (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hfit : pa+32*4 ≤ 8192) :
    GasSteps (l1At 4625 s c r bi pa pb 4 i 0 dst ret rest)
      (midAt s (cacheL1 c bi pa 4 4).cache r (cacheL1 c bi pa 4 4).carry bi
        pa pb 4 i dst ret rest) := by
  have hd := l1Dispatch s env blocks c r bi pa pb 4 i 0 dst ret rest hcap
  have hf : UInt256.isTrue (CiosCached.isFour 4) := by decide
  simp only [if_pos hf] at hd
  refine hd.trans ?_
  refine (l1Join s env blocks c r bi pa pb 4 i 0 dst ret rest hcap).trans ?_
  refine (l1Step 4783 s env c r bi pa pb 4 i 0 dst ret rest blocks.l1Mac4 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4821 s env c r bi pa pb 4 i 1 dst ret rest blocks.l1Mac5 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4854 s env c r bi pa pb 4 i 2 dst ret rest blocks.l1Mac6 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  exact l1Last s env blocks c r bi pa pb 4 i dst ret rest hcap hact (by decide) (by decide) hpa hfit

opaque l2Four (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hread : r.Valid c.virtual 4) :
    GasSteps (l2At 4953 s c r bi mu c0 pa pb 4 i 0 dst ret rest)
      (tailAt s (cacheL2 c mu c0 4 3).cache r (cacheL2 c mu c0 4 3).carry mu bi
        pa pb 4 i dst ret rest) := by
  have hd := l2Dispatch s env blocks c r bi mu c0 pa pb 4 i 0 dst ret rest hcap
  have hf : UInt256.isTrue (CiosCached.isFour 4) := by decide
  simp only [if_pos hf] at hd
  refine hd.trans ?_
  refine (l2Join s env blocks c r bi mu c0 pa pb 4 i 0 dst ret rest hcap).trans ?_
  refine (l2Step 5111 s env c r bi mu c0 pa pb 4 i 0 dst ret rest blocks.l2Mac4 hcap hact (by decide) (by decide) hread).trans ?_
  refine (l2Step 5146 s env c r bi mu c0 pa pb 4 i 1 dst ret rest blocks.l2Mac5 hcap hact (by decide) (by decide) hread).trans ?_
  exact l2Step 5176 s env c r bi mu c0 pa pb 4 i 2 dst ret rest blocks.l2Mac6 hcap hact (by decide) (by decide) hread

opaque l1Eight (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi : UInt256)
    (pa pb i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hpa : 32 ≤ pa) (hfit : pa+32*8 ≤ 8192) :
    GasSteps (l1At 4625 s c r bi pa pb 8 i 0 dst ret rest)
      (midAt s (cacheL1 c bi pa 8 8).cache r (cacheL1 c bi pa 8 8).carry bi
        pa pb 8 i dst ret rest) := by
  have hd := l1Dispatch s env blocks c r bi pa pb 8 i 0 dst ret rest hcap
  have hf : ¬UInt256.isTrue (CiosCached.isFour 8) := by decide
  simp only [if_neg hf] at hd
  refine hd.trans ?_
  refine (l1Step 4630 s env c r bi pa pb 8 i 0 dst ret rest blocks.l1Mac0 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4668 s env c r bi pa pb 8 i 1 dst ret rest blocks.l1Mac1 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4706 s env c r bi pa pb 8 i 2 dst ret rest blocks.l1Mac2 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4744 s env c r bi pa pb 8 i 3 dst ret rest blocks.l1Mac3 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Join s env blocks c r bi pa pb 8 i 4 dst ret rest hcap).trans ?_
  refine (l1Step 4783 s env c r bi pa pb 8 i 4 dst ret rest blocks.l1Mac4 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4821 s env c r bi pa pb 8 i 5 dst ret rest blocks.l1Mac5 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  refine (l1Step 4854 s env c r bi pa pb 8 i 6 dst ret rest blocks.l1Mac6 hcap hact (by decide) (by decide) hpa hfit).trans ?_
  exact l1Last s env blocks c r bi pa pb 8 i dst ret rest hcap hact (by decide) (by decide) hpa hfit

opaque l2Eight (s : State) (env : Environment art .Osaka s) (blocks : KernelBlocks art)
    (c : CachedMemory) (r : ReadOnlyCache) (bi mu c0 : UInt256)
    (pa pb i : Nat) (dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat)
    (hread : r.Valid c.virtual 8) :
    GasSteps (l2At 4953 s c r bi mu c0 pa pb 8 i 0 dst ret rest)
      (tailAt s (cacheL2 c mu c0 8 7).cache r (cacheL2 c mu c0 8 7).carry mu bi
        pa pb 8 i dst ret rest) := by
  have hd := l2Dispatch s env blocks c r bi mu c0 pa pb 8 i 0 dst ret rest hcap
  have hf : ¬UInt256.isTrue (CiosCached.isFour 8) := by decide
  simp only [if_neg hf] at hd
  refine hd.trans ?_
  refine (l2Step 4958 s env c r bi mu c0 pa pb 8 i 0 dst ret rest blocks.l2Mac0 hcap hact (by decide) (by decide) hread).trans ?_
  refine (l2Step 4996 s env c r bi mu c0 pa pb 8 i 1 dst ret rest blocks.l2Mac1 hcap hact (by decide) (by decide) hread).trans ?_
  refine (l2Step 5034 s env c r bi mu c0 pa pb 8 i 2 dst ret rest blocks.l2Mac2 hcap hact (by decide) (by decide) hread).trans ?_
  refine (l2Step 5072 s env c r bi mu c0 pa pb 8 i 3 dst ret rest blocks.l2Mac3 hcap hact (by decide) (by decide) hread).trans ?_
  refine (l2Join s env blocks c r bi mu c0 pa pb 8 i 4 dst ret rest hcap).trans ?_
  refine (l2Step 5111 s env c r bi mu c0 pa pb 8 i 4 dst ret rest blocks.l2Mac4 hcap hact (by decide) (by decide) hread).trans ?_
  refine (l2Step 5146 s env c r bi mu c0 pa pb 8 i 5 dst ret rest blocks.l2Mac5 hcap hact (by decide) (by decide) hread).trans ?_
  exact l2Step 5176 s env c r bi mu c0 pa pb 8 i 6 dst ret rest blocks.l2Mac6 hcap hact (by decide) (by decide) hread

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Gas
