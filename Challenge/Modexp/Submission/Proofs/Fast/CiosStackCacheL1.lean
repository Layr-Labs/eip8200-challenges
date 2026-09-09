import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMacOps

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

def cachedL1Body (k : Fin 3) : List Instr :=
  (((load1Program ++ L1.productProgram) ++ cacheLoad1 k) ++ L1.sumProgram) ++ cacheStore k

/-- The changed first-loop MAC reads and replaces a stack-resident accumulator
word. The product and carry arithmetic are the accepted kernel's lemmas. -/
theorem run_cachedL1Body (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (k : Fin 3) (pa carry bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pa.toNat 32) = s.activeWords) :
    runInstructions (cachedL1Body k)
      (framed s pc ([pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 31 pc)
      ([pa, macCarry (MachineState.readWord s.memory pa.toNat) bi (word c k) carry, bi] ++
        rowFrame (c.write (addr k)
          (macSum (MachineState.readWord s.memory pa.toNat) bi (word c k) carry))
          r pbi paEnd pbEnd flag dst ret rest)) := by
  let x := MachineState.readWord s.memory pa.toNat
  let frame := rowFrame c r pbi paEnd pbEnd flag dst ret rest
  have hrest : frame.length+7 < 1024 := by
    simp only [frame, rowFrame, cacheTail, List.length_append, List.length_cons, List.length_nil]
    omega
  have h1 := run_load1Program s pc c r pbi paEnd pbEnd flag dst ret pa carry bi rest hcap hactive
  have h2 := L1.run_product s (advancePC 3 pc) x bi carry pa frame hrest
  have h3 := run_cacheLoad1 s (advancePC 18 (advancePC 3 pc)) c r
    pbi paEnd pbEnd flag dst ret k (partialCarry x bi carry) pa (x*bi+carry) bi rest hcap
  have h4 := L1.run_sum s (advancePC 2 (advancePC 18 (advancePC 3 pc)))
    (word c k) (x*bi+carry) (partialCarry x bi carry) bi pa frame hrest
  rw [carry_eq, sum_eq] at h4
  have h5 := run_cacheStore s (advancePC 6 (advancePC 2 (advancePC 18 (advancePC 3 pc))))
    c r pbi paEnd pbEnd flag dst ret k (macSum x bi (word c k) carry)
    pa (macCarry x bi (word c k) carry) bi rest hcap
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  have h1234 := runInstructions_append_some _ _ _ _ _ h123 h4
  have h12345 := runInstructions_append_some _ _ _ _ _ h1234 h5
  simpa only [cachedL1Body, x, frame, advancePC] using h12345

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_cachedL1Body
