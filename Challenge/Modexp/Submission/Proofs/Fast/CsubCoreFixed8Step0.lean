import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreFixed8Entry
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
theorem run_csFixedStep8_0 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep8_0
      (csFixedState s memory 8 0 4896 pdst ret rest) =
      some (csFixedState s memory 8 1 4912 pdst ret rest) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 224 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2336 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 2016 32 (by decide) (by decide) hact
  have hstep : csStep memory 8 1 =
      (let prev := csStep memory 8 0
       let t := MachineState.readWord prev.memory (2112 + 32 * (8 - 1 - 0))
       let md := MachineState.readWord prev.memory (32 * (8 - 1 - 0))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (1792 + 32 * (8 - 1 - 0))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 8 0
  have hword224 : (224 : UInt256).toNat = 224 := by decide
  have hword8480 : (2336 : UInt256).toNat = 2336 := by decide
  have hword7392 : (2016 : UInt256).toNat = 2016 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep8_0, csFixedState, fixedOrComm, hstep, csStep, fixedSubtractZero, hrun,
      hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword224, hword8480, hword7392, List.exchange]
  try (split <;> decide)


end Challenge.Modexp.Submission.Proofs.Fast.Csub
