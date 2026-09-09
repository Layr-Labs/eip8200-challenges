import Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBodyState

set_option warningAsError true
set_option maxHeartbeats 200000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.CiosCached

theorem run_zero (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1006)
    (hact : 296 ≤ s.activeWords.toNat) (hn : n ≤ 32)
    (hcds : s.executionEnv.calldata.size < 2^256)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram (cachedEntryState s mem pa pb n dst ret rest) =
      some (clearedState s mem pa pb n dst ret rest) := by
  have hc6 : rest.length+7 < 1024 := by omega
  have hc7 : rest.length+8 < 1024 := by omega
  have hc8 : rest.length+9 < 1024 := by omega
  have hc9 : rest.length+10 < 1024 := by omega
  have hc10 : rest.length+11 < 1024 := by omega
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have hsizeN : (64+32*n) %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      64+32*n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      s.executionEnv.calldata.size := Nat.mod_eq_of_lt (by omega)
  have hactS : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8192 (64+32*n)) =
      s.activeWords := activeWords_fix s 8192 (64+32*n) (by omega) (by omega) hact
  simp [zeroProgram, entryProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    cachedEntryState, clearedState, mpZeroed, hc6, hc7, hc8, hc9, hc10, h64, h8192, h9344, hs32,
    hsizeN, hcdsN, hactS, hactC, State.activeWordsAfterUInt256,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.CiosStackCacheInitBody
