import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Tail

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTableMemory
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheModel

def loadHead : List Instr := CiosStackCachePrograms.tailStore.take 4
def storeCached : List Instr := (CiosStackCachePrograms.tailStore.drop 4).take 3
def storeHigh : List Instr := CiosStackCachePrograms.tailStore.drop 7

theorem split_store : CiosStackCachePrograms.tailStore = (loadHead ++ storeCached) ++ storeHigh := rfl

set_option linter.unusedSimpArgs false in
theorem run_cleanup (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (carry mu bi : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions CiosStackCachePrograms.tailCleanup
      (framed s (UInt256.ofNat 4824) ([carry, mu, bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4827) ([carry] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  simp [CiosStackCachePrograms.tailCleanup, CiosStackCachePrograms.tailStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, CachedMemory.write,
    h16, h17, h18, h19, h20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_loadHead (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (carry : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions loadHead
      (framed s (UInt256.ofNat 4827) ([carry] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4833) ([MachineState.readWord s.memory 8224 + carry, carry] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have hp8192 : (8192 : UInt256).toNat = 8192 := by decide
  have ha8192 := activeWords_fix s 8192 32 (by decide) (by omega) hact
  have hp8224 : (8224 : UInt256).toNat = 8224 := by decide
  have ha8224 := activeWords_fix s 8224 32 (by decide) (by omega) hact
  simp [loadHead, CiosStackCachePrograms.tailStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, CachedMemory.write,
    h16, h17, h18, h19, h20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat, hp8192, hp8224, ha8192, ha8224, State.activeWordsAfterUInt256, storeWord]

set_option linter.unusedSimpArgs false in
theorem run_storeCached (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (sum carry : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions storeCached
      (framed s (UInt256.ofNat 4833) ([sum, carry] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (UInt256.ofNat 4836) ([sum, carry] ++ rowFrame (c.write 8256 sum) r pbi paEnd pbEnd flag dst ret rest)) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  simp [storeCached, CiosStackCachePrograms.tailStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, CachedMemory.write,
    h16, h17, h18, h19, h20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_storeHigh (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256) (sum carry : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions storeHigh
      (framed s (UInt256.ofNat 4836) ([sum, carry] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed { s with memory := storeWord s.memory 8224 (MachineState.readWord s.memory 8192 + UInt256.lt sum carry) } (UInt256.ofNat 4846) (rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have hp8192 : (8192 : UInt256).toNat = 8192 := by decide
  have ha8192 := activeWords_fix s 8192 32 (by decide) (by omega) hact
  have hp8224 : (8224 : UInt256).toNat = 8224 := by decide
  have ha8224 := activeWords_fix s 8224 32 (by decide) (by omega) hact
  simp [storeHigh, CiosStackCachePrograms.tailStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, CachedMemory.write,
    h16, h17, h18, h19, h20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat, hp8192, hp8224, ha8192, ha8224, State.activeWordsAfterUInt256, storeWord]

set_option linter.unusedSimpArgs false in
theorem run_test (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (htarget : Decode.isValidJumpDest s.executionEnv.code 4243 = true) :
    runInstructions CiosStackCachePrograms.tailTest
      (framed s (UInt256.ofNat 4846) (rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (if UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) then UInt256.ofNat 4243 else UInt256.ofNat 4855) (rowFrame c r (negative32+pbi) paEnd pbEnd flag dst ret rest)) := by
  have h16 : rest.length+16 < 1024 := by omega
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  by_cases ht : UInt256.isTrue (UInt256.gt (negative32+pbi) pbEnd) <;>
  simp [CiosStackCachePrograms.tailTest, CiosStackCachePrograms.tailStore, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, CachedMemory.write,
    h16, h17, h18, h19, h20, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.word_toNat_ofNat, ht, htarget]

theorem cacheTail_eq (c : CachedMemory) (carry : UInt256) :
    CiosStackCacheModel.cacheTail c carry =
      { memory := storeWord c.memory 8224
          (MachineState.readWord c.memory 8192 +
            UInt256.lt (MachineState.readWord c.memory 8224 + carry) carry)
        t0 := MachineState.readWord c.memory 8224 + carry
        t1 := c.t1
        t2 := c.t2 } := by
  unfold CiosStackCacheModel.cacheTail
  rw [virtual_read_disjoint c 8224 (by omega)]
  dsimp only
  rw [virtual_read_disjoint _ 8192 (by omega)]
  rfl

theorem run_store (s : State) (c : CachedMemory) (r : ReadOnlyCache)
    (pbi paEnd pbEnd flag dst ret carry : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 998) (hact : 296 ≤ s.activeWords.toNat) :
    runInstructions CiosStackCachePrograms.tailStore
      (framed { s with memory := c.memory } (UInt256.ofNat 4827)
        ([carry] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed { s with memory := (CiosStackCacheModel.cacheTail c carry).memory }
      (UInt256.ofNat 4846)
      (rowFrame (CiosStackCacheModel.cacheTail c carry) r pbi paEnd pbEnd flag dst ret rest)) := by
  let sum := MachineState.readWord c.memory 8224 + carry
  have h1 := run_loadHead { s with memory := c.memory } c r pbi paEnd pbEnd flag dst ret carry rest hcap hact
  have h2 := run_storeCached { s with memory := c.memory } c r pbi paEnd pbEnd flag dst ret sum carry rest hcap
  have h3 := run_storeHigh { s with memory := c.memory } (c.write 8256 sum) r
    pbi paEnd pbEnd flag dst ret sum carry rest hcap hact
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  simpa only [split_store, cacheTail_eq, sum, rowFrame, cacheTail, CachedMemory.write, ite_true] using h123

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Tail

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Tail.run_store
