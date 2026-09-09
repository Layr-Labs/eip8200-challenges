import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCachePrograms
import Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached
open Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheMemory
open Challenge.Modexp.Submission.Proofs.Fast.CiosEndAroundCarry

namespace Mid

def loadMu : List Instr := CiosStackCachePrograms.midProduct.take 6
def multiply : List Instr := (CiosStackCachePrograms.midProduct.drop 6).take 4
def foldCarry : List Instr := CiosStackCachePrograms.midProduct.drop 10

theorem split_program : CiosStackCachePrograms.midProduct = (loadMu ++ multiply) ++ foldCarry := rfl

set_option linter.unusedSimpArgs false in
theorem run_loadMu (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998) (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat r.tl.toNat 32) = s.activeWords) :
    runInstructions loadMu
      (framed s pc ([] ++ ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest))) =
    some (framed s (advancePC 6 pc) ([r.inv * MachineState.readWord s.memory r.tl.toNat, r.inv * MachineState.readWord s.memory r.tl.toNat, MachineState.readWord s.memory r.tl.toNat] ++ ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest))) := by
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  simp [loadMu, CiosStackCachePrograms.midProduct, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, endCarry,
    h17, h18, h19, h20, h21, h22, advancePC, allOnes_value, List.exchange, State.activeWordsAfterUInt256, hactive]

set_option linter.unusedSimpArgs false in
theorem run_multiply (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (bi pbi paEnd pbEnd flag dst ret : UInt256) (mu t : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions multiply
      (framed s pc ([mu, mu, t] ++ ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest))) =
    some (framed s (advancePC 4 pc) ([UInt256.mulMod mu r.m0 maxWord, mu, t] ++ ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest))) := by
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  simp [multiply, CiosStackCachePrograms.midProduct, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, endCarry,
    h17, h18, h19, h20, h21, h22, advancePC, allOnes_value, List.exchange]

set_option linter.unusedSimpArgs false in
theorem run_foldCarry (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (bi pbi paEnd pbEnd flag dst ret : UInt256) (mm mu t : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)  :
    runInstructions foldCarry
      (framed s pc ([mm, mu, t] ++ ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest))) =
    some (framed s (advancePC 8 pc) ([endCarry mm t, mu] ++ ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest))) := by
  have h17 : rest.length+17 < 1024 := by omega
  have h18 : rest.length+18 < 1024 := by omega
  have h19 : rest.length+19 < 1024 := by omega
  have h20 : rest.length+20 < 1024 := by omega
  have h21 : rest.length+21 < 1024 := by omega
  have h22 : rest.length+22 < 1024 := by omega
  simp [foldCarry, CiosStackCachePrograms.midProduct, runInstructions,
    Challenge.EvmProof.Stepper.runInstr, framed, rowFrame, cacheTail, endCarry,
    h17, h18, h19, h20, h21, h22, advancePC, allOnes_value, List.exchange]

theorem run_words (s : State) (pc : UInt256) (c : CachedMemory) (r : ReadOnlyCache)
    (bi pbi paEnd pbEnd flag dst ret : UInt256)
    (rest : List UInt256) (hcap : rest.length ≤ 998)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat r.tl.toNat 32) = s.activeWords)
    (hminv : (r.m0.toNat * r.inv.toNat + 1) % 2^256 = 0) :
    runInstructions CiosStackCachePrograms.midProduct
      (framed s pc ([bi] ++ rowFrame c r pbi paEnd pbEnd flag dst ret rest)) =
    some (framed s (advancePC 18 pc)
      ([UInt256.isZero (UInt256.isZero
          (r.m0 * (r.inv * MachineState.readWord s.memory r.tl.toNat))) +
          mulHi r.m0 (r.inv * MachineState.readWord s.memory r.tl.toNat),
        r.inv * MachineState.readWord s.memory r.tl.toNat, bi] ++
          rowFrame c r pbi paEnd pbEnd flag dst ret rest)) := by
  let t := MachineState.readWord s.memory r.tl.toNat
  let mu := r.inv*t
  have h1 := run_loadMu s pc c r bi pbi paEnd pbEnd flag dst ret rest hcap hactive
  have h2 := run_multiply s (advancePC 6 pc) c r bi pbi paEnd pbEnd flag dst ret mu t rest hcap
  have h3 := run_foldCarry s (advancePC 4 (advancePC 6 pc)) c r bi pbi paEnd pbEnd flag dst ret
    (UInt256.mulMod mu r.m0 maxWord) mu t rest hcap
  have hc := row_carry r.m0 r.inv t hminv
  rw [mulMod_comm] at hc
  have h12 := runInstructions_append_some _ _ _ _ _ h1 h2
  have h123 := runInstructions_append_some _ _ _ _ _ h12 h3
  rw [← split_program] at h123
  simpa only [mu, hc, t, advancePC, List.nil_append, List.append_assoc,
    List.cons_append] using h123

end Mid
end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache

#print axioms Challenge.Modexp.Submission.Proofs.Fast.CiosStackCache.Mid.run_words
