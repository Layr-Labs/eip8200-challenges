import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedRowFrames

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCached

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open WindowNibbleKernel

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_out (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1006) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (_hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    runInstructions outProgram
      (outState s mem pa pb n i pdst ret rest) =
      some (l1At 4578 s mem (rowBi mem pb n i) pa pb n i 0 pdst ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hpbi : ptrAt (pb + 32 * n - 32) i %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hpa32 : 32 + (pa - 32) = pa := by omega
  have hsuba : UInt256.ofNat (32 * n + pa) - UInt256.ofNat 32 =
      UInt256.ofNat (pa + 32 * n - 32) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    exact congrArg UInt256.ofNat (by omega)
  have hsubaN : 32 * n + (pa - 32) = pa + 32 * n - 32 := by omega
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - i)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  have hactT : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) = s.activeWords :=
    activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hactS : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) = s.activeWords :=
    activeWords_fix s 9344 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [outProgram, runInstructions, isFour, negative32, allOnes,
      negative32_not, allOnes_not,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      outState, l1At, l1Step, rowBi, fastPC10, fastPC11,
      hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15, hc16, hc17, hrun, h32, h9344, h9440, hzero,
      hs32, htl, hpbi, hpa32, hsuba, hsubaN, hactB, hactT, hactS,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
