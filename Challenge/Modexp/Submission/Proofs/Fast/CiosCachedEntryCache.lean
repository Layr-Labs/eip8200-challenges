import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 100000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

/-- Internal state for the mask template. Its leading JUMPDEST is removed
when composing the actual entry trace. -/
def maskEntryState (s : State) (mem : ByteArray) (pa pb : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { entryState s mem pa pb pdst ret rest with pc := UInt256.ofNat 4476 }

def cacheProgram : List Instr := entryProgram.take 13
def entryBodyProgram : List Instr := entryProgram.drop 13

theorem entryProgram_split : entryProgram = cacheProgram ++ entryBodyProgram := by
  exact (List.take_append_drop 13 entryProgram).symm

def cachedEntryState (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 4524
           stack := [UInt256.ofNat pa, UInt256.ofNat pb,
             isFour n, negative32, allOnes, pdst, ret] ++ rest
           memory := mem }

set_option linter.unusedSimpArgs false in
theorem run_cache (s : State) (mem : ByteArray) (pa pb n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hact : 296 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions cacheProgram (maskEntryState s mem pa pb pdst ret rest) =
      some (cachedEntryState s mem pa pb n pdst ret rest) := by
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
  have hnegative : (115792089237316195423570985008687907853269984665640564039457584007913129639904 : UInt256) = negative32 := by decide
  simp [cacheProgram, entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    maskEntryState, entryState, cachedEntryState, isFour, hc4, hc5, hc6, hc7, hc8,
    hnegative, ← allOnes_not, h128, h9344, hs32, hactS, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    List.exchange]
  decide


end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
