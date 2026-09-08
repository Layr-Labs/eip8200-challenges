import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryDefs

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryOut

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNRowPrograms MonproKNRowFrames MonproKNCache MonproKNEntryDefs
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem run_out (s : State) (mem : ByteArray) (pa pb n i : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1007)
    (hact : 296 ≤ s.activeWords.toNat)
    (_hn : 2 ≤ n) (_hn32 : n ≤ 32) (hi : i < n)
    (hpa : 32 ≤ pa) (_hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord mem 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord mem 9440 = UInt256.ofNat (8224 + 32 * n)) :
    runInstructions outProgram
      (outer s mem pa pb n i pdst ret rest) =
      some (l1 s mem (rowBi mem pb n i) pa pb n i 0 2003 pdst ret rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hpbi : ptrAt (pb + 32 * n - 32) i %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
      pb + 32 * (n - 1 - i) := by
    rw [ptrAt_mod _ _ (by omega) (by omega)]; omega
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
  have hp0 : ptrAt (pa+32*n-32) 0 = pa+32*n-32 := by simp [ptrAt]
  have ht0 : ptrAt (8224+32*n) 0 = 8224+32*n := by simp [ptrAt]
  simp
    [outProgram, runInstructions,
      Challenge.EvmProof.Stepper.runInstr,
      outer, l1, l1Step, rowBi,
      hc7, hc8, hc9, hc10, hc11, hc12, h9344, h9440, hzero,
      hs32, htl, hpbi, hp0, ht0, hsubaN, hactB, hactT, hactS,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      ]

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNEntryOut
