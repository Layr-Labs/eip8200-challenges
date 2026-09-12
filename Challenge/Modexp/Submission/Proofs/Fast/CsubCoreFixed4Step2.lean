import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreFixed4Step1
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
theorem run_csFixedStep4_2 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedStep4_2
      (csFixedState s memory 4 2 5028 pdst ret rest) =
      some (csFixedState s memory 4 3 5051 pdst ret rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have ha0 := activeWords_fix s 32 32 (by decide) (by decide) hact
  have ha1 := activeWords_fix s 2144 32 (by decide) (by decide) hact
  have ha2 := activeWords_fix s 1824 32 (by decide) (by decide) hact
  have hstep : csStep memory 4 3 =
      (let prev := csStep memory 4 2
       let t := MachineState.readWord prev.memory (2112 + 32 * (4 - 1 - 2))
       let md := MachineState.readWord prev.memory (32 * (4 - 1 - 2))
       let d1 := t - md
       let d2 := d1 - prev.flag
       { memory := MachineState.writeBytes prev.memory
           (Data.Bytes.natToBytesPadded d2.toNat 32) (1792 + 32 * (4 - 1 - 2))
         flag := UInt256.lor (UInt256.lt t md) (UInt256.lt d1 prev.flag) } : LimbState) := csStep.eq_2 memory 4 2
  have hword32 : (32 : UInt256).toNat = 32 := by decide
  have hword8288 : (2144 : UInt256).toNat = 2144 := by decide
  have hword7200 : (1824 : UInt256).toNat = 1824 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedStep4_2, csFixedState, fixedOrComm, hstep, hrun,
      hc3, hc4, hc5, hc6, hc7, hc8, hc9, ha0, ha1, ha2, UInt256.gt, UInt256.lt,
      opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword32, hword8288, hword7200, List.exchange]


end Challenge.Modexp.Submission.Proofs.Fast.Csub
