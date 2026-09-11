import Challenge.Modexp.Submission.Proofs.Fast.CsubCorePart15

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

theorem run_amTail (s : State) (memory : ByteArray) (pa pb n j : Nat)
    (pd ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hact : 296 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock blk1662
      (amTailState s memory pa pb n j pd ret rest) =
      some (csEntryState s
        (MachineState.writeBytes (amStep memory pa pb n j).memory
          (Data.Bytes.natToBytesPadded (amStep memory pa pb n j).flag.toNat 32) 8224)
        pd ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have h8224 : (8224 : UInt256).toNat = 8224 := by decide
  have hactT : UInt256.ofNat (MachineState.activeWordsAfter s.activeWords.toNat 8224 32) =
      s.activeWords := activeWords_fix s 8224 32 (by decide) (by omega) hact
  simp (config := { maxSteps := 400000 })
    [blk1662, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,
      Challenge.EvmProof.Stepper.runInstr,
      amTailState, csEntryState, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hc2, hc3, hc4, hc5, hc6, hrun, h8224, hactT,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
