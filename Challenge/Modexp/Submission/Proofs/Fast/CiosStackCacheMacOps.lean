import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheFrames

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory

set_option linter.unusedSimpArgs false in
theorem run_load1Program (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (pa carry bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat pa.toNat 32) = s.activeWords) :
    runInstructions load1Program
      (framed s pc ([pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 3 pc) ([maxWord, MachineState.readWord s.memory pa.toNat, pa, carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  have h23 : rest.length+23 < 1024 := by omega

  simp [load1Program, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, word, addr, sourceWord, CachedMemory.write,
    h18, h19, h20, h21, h22, h23, advancePC, allOnes_value,
    List.exchange, State.activeWordsAfterUInt256, hactive]

set_option linter.unusedSimpArgs false in
theorem run_cacheLoad1 (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (k : Fin 3) (part pa sum y : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions (cacheLoad1 k)
      (framed s pc ([part, pa, sum, y] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 2 pc) ([word c k, sum, part, pa, sum, y] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  have h23 : rest.length+23 < 1024 := by omega

  fin_cases k <;> simp [cacheLoad1, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, word, addr, sourceWord, CachedMemory.write,
    h18, h19, h20, h21, h22, h23, advancePC, allOnes_value,
    List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_cacheLoad2 (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (k : Fin 3) (part sum y bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions (cacheLoad2 k)
      (framed s pc ([part, sum, y, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 2 pc) ([word c k, sum, part, sum, y, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  have h23 : rest.length+23 < 1024 := by omega

  fin_cases k <;> simp [cacheLoad2, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, word, addr, sourceWord, CachedMemory.write,
    h18, h19, h20, h21, h22, h23, advancePC, allOnes_value,
    List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_cacheStore (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (k : Fin 3) (sum a b d : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions (cacheStore k)
      (framed s pc ([sum, a, b, d] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 2 pc) ([a, b, d] ++ rowFrame (c.write (addr k) sum) r pbi paEnd pbEnd flag dst ret rest)) := by
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  have h23 : rest.length+23 < 1024 := by omega

  fin_cases k <;> simp [cacheStore, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, word, addr, sourceWord, CachedMemory.write,
    h18, h19, h20, h21, h22, h23, advancePC, allOnes_value,
    List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_sourceLoad2 (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (k : Fin 2) (carry mu bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions (sourceLoad2 k)
      (framed s pc ([carry, mu, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 2 pc) ([maxWord, sourceWord r k, carry, mu, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  have h23 : rest.length+23 < 1024 := by omega

  fin_cases k <;> simp [sourceLoad2, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, word, addr, sourceWord, CachedMemory.write,
    h18, h19, h20, h21, h22, h23, advancePC, allOnes_value,
    List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.run_cacheStore
