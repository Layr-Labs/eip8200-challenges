import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

def cacheProgram : List Instr := entryProgram.take 19
def entryBodyProgram : List Instr := entryProgram.drop 19

theorem entryProgram_split : entryProgram = cacheProgram ++ entryBodyProgram := by
  exact (List.take_append_drop 19 entryProgram).symm

def cachedEntryState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4509
           stack := [UInt256.ofNat pa, UInt256.ofNat pb,
             l1Target n, negative32, allOnes, l2Target n, pdst, ret] ++ rest
           memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_cache (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions cacheProgram (entryState s mem pa pb pdst ret rest) =
      some (cachedEntryState s mem pa pb n pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by decide) (by omega) hact
  have h128 : (128 : UInt256) = UInt256.ofNat 128 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  simp [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, cacheProgram, entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    entryState, cachedEntryState, l1Target, l2Target, isFour, hc4, hc5, hc6, hc7, hc8,
    ← negative32_not, ← allOnes_not, h128, h9344, hs32, hactS, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    List.exchange]
  exact ⟨rfl, rfl, rfl, rfl⟩


end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
