import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart09

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

theorem run_amEntry (s : State) (memory : ByteArray) (pa pb n : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat)
    (hn : 2 ≤ n) (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472)
    (hpb : 32 ≤ pb) (hpbFit : pb + 32 * n ≤ 9472)
    (hs32 : MachineState.readWord memory 9344 = UInt256.ofNat (32 * n))
    (htl : MachineState.readWord memory 9440 = UInt256.ofNat (8224 + 32 * n)) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1600
      (amEntryState s memory pa pb pd ret rest) =
      some (amLoopState s memory pa pb n 0 pd ret rest) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h9344 : (9344 : UInt256).toNat = 9344 := by decide
  have h9440 : (9440 : UInt256).toNat = 9440 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hactA : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9344 32) =
      s.activeWords := activeWords_fix s 9344 32 (by decide) (by omega) hact
  have hactB : UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat 9440 32) =
      s.activeWords := activeWords_fix s 9440 32 (by decide) (by omega) hact
  have hsuba : UInt256.ofNat (pa + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (pa + 32 * n - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  have hsubb : UInt256.ofNat (pb + 32 * n) - UInt256.ofNat 32 =
      UInt256.ofNat (pb + 32 * n - 32) :=
    Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)
  simp (config := { maxSteps := 800000 })
    [blk1600, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amEntryState, amLoopState, amStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc4, hc5, hc6, hc7, hc8, hrun, h32, h9344, h9440, hzero,
      hs32, htl, hactA, hactB, hsuba, hsubb,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
