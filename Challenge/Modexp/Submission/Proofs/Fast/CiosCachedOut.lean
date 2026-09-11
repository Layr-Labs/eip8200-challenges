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

set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem run_out (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1005) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (_hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472) :
    runInstructions outProgram
      (outState s mem pa pb n i pdst ret rest) =
      some (firstAt 4172 s mem (rowBi mem pb n i) pa pb n i pdst ret rest) := by
  have hExtra9 : rest.length + 9 < 1024 := by omega
  have hExtra10 : rest.length + 10 < 1024 := by omega
  have hExtra11 : rest.length + 11 < 1024 := by omega
  have hExtra12 : rest.length + 12 < 1024 := by omega
  have hExtra13 : rest.length + 13 < 1024 := by omega
  have hExtra14 : rest.length + 14 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hpbi : ptrAt (pb + 32 * n - 32) i %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]
    omega
  have hactB : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat
      (pb + 32 * (n - 1 - i)) 32) = s.activeWords :=
    activeWords_fix s _ 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 800000 })
    [hExtra9, hExtra10, hExtra11, hExtra12, hExtra13, hExtra14, outProgram, runInstructions,
      Challenge.EvmProof.Stepper.runInstr,
      outState, firstAt, l1At, l1Step, rowBi,
      hc8, hc9, hc10, hc11, hzero, hpbi, hactB,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.CiosCached
