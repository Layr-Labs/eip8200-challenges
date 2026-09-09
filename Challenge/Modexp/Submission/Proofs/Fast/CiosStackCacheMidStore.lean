import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Mid

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

set_option linter.unusedSimpArgs false in
theorem run_storeWords (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (carry bi pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions CiosStackCachePrograms.midStore
      (framed s (UInt256.ofNat 4890) ([carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed { s with memory := midMem s.memory carry } (UInt256.ofNat 4906)
      ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have hpN : (8224 : UInt256).toNat = 8224 := by decide
  have hpP : (8192 : UInt256).toNat = 8192 := by decide
  have haN := activeWords_fix s 8224 32 (by decide) (by omega) hact
  have haP := activeWords_fix s 8192 32 (by decide) (by omega) hact
  simp [CiosStackCachePrograms.midStore, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    framed, rowFrame, cacheTail, midMem, midMem1, h18, h19, h20, h21, hpN, hpP, haN, haP,
    State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem cacheMid_eq (c : CachedMemory) (carry : UInt256) :
    cacheMid c carry =
      { memory := midMem c.memory carry, t0 := c.t0, t1 := c.t1, t2 := c.t2 } := by
  unfold cacheMid
  rw [virtual_read_disjoint c 8224 (by omega)]
  rfl

theorem run_store (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (carry bi pbi paEnd pbEnd flag dst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions CiosStackCachePrograms.midStore
      (framed { s with memory := c.memory } (UInt256.ofNat 4890)
        ([carry, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed { s with memory := (cacheMid c carry).memory } (UInt256.ofNat 4906)
      ([bi] ++ rowFrame (cacheMid c carry) r pbi paEnd pbEnd flag dst ret rest)) := by
  simpa only [cacheMid_eq, rowFrame, cacheTail] using
    run_storeWords { s with memory := c.memory } c r carry bi pbi paEnd pbEnd flag dst ret rest hcap hact

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Mid

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Mid.run_store
