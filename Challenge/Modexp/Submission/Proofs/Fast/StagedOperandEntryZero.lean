import Challenge.Modexp.Submission.Proofs.Fast.StagedOperandMemory
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedEntryPointers

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Fast.StagedOperand

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast Monpro CiosCached

def zeroProgram : List Instr :=
  [.push 2 9344, .op .MLOAD,
   .op (.Dup ⟨0, by decide⟩), .op (.Dup ⟨2, by decide⟩), .push 2 8960, .op .MCOPY,
   .op (.Dup ⟨0, by decide⟩), .push 1 64, .op .ADD, .op .CALLDATASIZE,
   .push 2 8192, .op .CALLDATACOPY]

theorem run_zero (s : State) (mem : ByteArray) (pa pb n : Nat)
    (dst ret : UInt256) (rest : List UInt256) (hcap : rest.length ≤ 1005)
    (hact : 296 ≤ s.activeWords.toNat) (hnpos : 0 < n) (hn : n ≤ 8) (hpa : pa+32*n ≤ 9472)
    (hcds : s.executionEnv.calldata.size < 115792089237316195423570985008687907853269984665640564039457584007913129639936)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32*n)) :
    runInstructions zeroProgram
      {cachedEntryState s mem pa pb n dst ret rest with pc := UInt256.ofNat 4129} =
      some (clearedState s (stage mem pa n) pa pb n dst ret rest) := by
  have hc8 : rest.length+8 < 1024 := by omega
  have hc9 : rest.length+9 < 1024 := by omega
  have hc10 : rest.length+10 < 1024 := by omega
  have hc11 : rest.length+11 < 1024 := by omega
  have hc12 : rest.length+12 < 1024 := by omega
  have hc13 : rest.length+13 < 1024 := by omega
  have hc14 : rest.length+14 < 1024 := by omega
  have hpaN : pa % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = pa := Nat.mod_eq_of_lt (by omega)
  have hszN : (32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 32*n := Nat.mod_eq_of_lt (by omega)
  have hsizeN : (64+32*n) % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = 64+32*n := Nat.mod_eq_of_lt (by omega)
  have hcdsN : s.executionEnv.calldata.size % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.executionEnv.calldata.size :=
    Nat.mod_eq_of_lt hcds
  have hactS := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactC := activeWords_fix s 8192 (64+32*n) (by omega) (by omega) hact
  have hactD := activeWordsAfter_fix s.activeWords.toNat 8960 (32*n) (by omega) (by omega) hact
  have hactA := activeWordsAfter_fix s.activeWords.toNat pa (32*n) (by omega) (by omega) hact
  have hactN : s.activeWords.toNat % 115792089237316195423570985008687907853269984665640564039457584007913129639936 = s.activeWords.toNat :=
    Nat.mod_eq_of_lt s.activeWords.val.isLt
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h8960 : (8960 : UInt256).toNat = 8960 := by decide
  have h8192 : (8192 : UInt256).toNat = 8192 := by decide
  have h64 : (64 : UInt256) = UInt256.ofNat 64 := by decide
  simp (config := { maxSteps := 200000 }) [zeroProgram, runInstructions, Challenge.EvmProof.Stepper.runInstr,
    cachedEntryState, clearedState, stage, mpZeroed, hs32,
    State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2, hactS, hactC, hactD, hactA,
    h9344, h8960, h8192, h64, hactN,
    Challenge.EvmProof.Word.succ_ofNat_mod, Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hpaN, hszN, hsizeN, hcdsN,
    hc8, hc9, hc10, hc11, hc12, hc13, hc14]

end Challenge.Modexp.Submission.Proofs.Fast.StagedOperand
