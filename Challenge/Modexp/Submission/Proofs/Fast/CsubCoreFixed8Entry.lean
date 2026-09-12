import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreBase
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
theorem run_csFixedEntry8 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat)
    (hs32 : MachineState.readWord memory 2784 = UInt256.ofNat (32 * 8)) :
    Challenge.EvmProof.Stepper.runLocatedBlock csFixedEntry8
      (subEntryState s memory pdst ret rest) =
      some (csFixedState s memory 8 0 4896 pdst ret rest) := by
  have hactS := activeWords_fix s 2784 32 (by decide) (by decide) hact
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hword9344 : (2784 : UInt256).toNat = 2784 := by decide
  have hword128 : (128 : UInt256).toNat = 128 := by decide
  have hword256 : (256 : UInt256).toNat = 256 := by decide
  have hword4972 : (4847 : UInt256).toNat = 4847 := by decide
  have hword5022 : (4895 : UInt256).toNat = 4895 := by decide
  have hword5131 : (4981 : UInt256).toNat = 4981 := by decide
  have hword2225 : (2026 : UInt256).toNat = 2026 := by decide
  have hwordEq4972 : (4847 : UInt256) = UInt256.ofNat 4847 := by decide
  have hwordEq5022 : (4895 : UInt256) = UInt256.ofNat 4895 := by decide
  have hwordEq5131 : (4981 : UInt256) = UInt256.ofNat 4981 := by decide
  have hwordEq2225 : (2026 : UInt256) = UInt256.ofNat 2026 := by decide
  have hwordZero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (config := { maxSteps := 800000 })
    [csFixedEntry8, subEntryState, csFixedState, csStep, fastPC14, fastPC15, fastPC16, fastPC17, fastPC18, fastPC19,
      hrun, hcode, hs32, hactS, hc2, hc3, hc4, hc5,
      UInt256.eq, UInt256.isTrue, opAt, pushAt, wfOp, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      State.activeWordsAfterUInt256, Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hword9344, hword128, hword256, hword4972, hword5022, hword5131, hword2225, hwordEq4972, hwordEq5022, hwordEq5131, hwordEq2225, hwordZero, List.exchange]


end Challenge.Modexp.Submission.Proofs.Fast.Csub
