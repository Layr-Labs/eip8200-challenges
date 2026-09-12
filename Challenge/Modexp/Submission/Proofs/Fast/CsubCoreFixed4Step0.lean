import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreFixed4Entry
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
attribute [local irreducible] csStep
set_option linter.unusedSimpArgs false in
theorem run_csFixedStep4_0 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_0
      (csFixedState s memory 4 0 4690 pdst ret rest) =
      some (csFixedState s memory 4 1 5004 pdst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 96 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2208 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1888 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 1 =
      (let prev := csStep memory 4 0
       let t := MachineState.readWord prev.memory (2112 + 32 * (4 - 1 - 0))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 0))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (1792 + 32 * (4 - 1 - 0))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 0
  have hword96 : (96 : UInt256).toNat = 96 := by decide
  have hword8352 : (2208 : UInt256).toNat = 2208 := by decide
  have hword7264 : (1888 : UInt256).toNat = 1888 := by decide
  have hword5117 : (5004 : UInt256).toNat = 5004 := by decide
  have hwordEq5117 : (5004 : UInt256) = UInt256.ofNat 5004 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_0, csFixedState, fixedOrComm, hstep, csStep, fixedSubtractZero, hrun, hcode,
      hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword96, hword8352, hword7264, hword5117, hwordEq5117, List.exchange]
  try (split <;> decide)


end Challenge.Modexp.Submission.Proofs.Fast.Csub
