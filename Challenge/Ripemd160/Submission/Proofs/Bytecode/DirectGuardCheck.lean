import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The first-word check that chooses between the two guards. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

theorem run_checkEntry (input : ByteArray)
    (href : referenceWord input = KnownInputData.fullWord) :
    run checkEntryPath (sizeMatched input) = some (loopState input 0) := by
  have hzero : UInt256.xor KnownInputData.fullWord (referenceWord input) = 0 := by
    exact (KnownInputLogic.wordXor_eq_zero_iff
      KnownInputData.fullWord (referenceWord input)).2 href.symm
  have hfalse : ¬ UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (referenceWord input)) := by
    rw [hzero]
    decide
  have hcond : ¬ UInt256.isTrue
      (UInt256.xor KnownInputData.fullWord (MachineState.readWord input 0)) := by
    simpa only [referenceWord] using hfalse
  have hstack : UInt256.xor KnownInputData.fullWord
      (MachineState.readWord input 0) =
      UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord :=
    BooleanSelect.xor_comm _ _
  have hcondStack : ¬ UInt256.isTrue
      (UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord) := by
    rw [← hstack]
    exact hcond
  have hstackZero :
      UInt256.xor (MachineState.readWord input 0) KnownInputData.fullWord =
        UInt256.ofNat 0 := by
    rw [← hstack, show UInt256.ofNat 0 = 0 by rfl]
    simpa only [referenceWord] using hzero
  have hzeroFalse : ¬ UInt256.isTrue (UInt256.ofNat 0) := by decide
  simp (config := { maxSteps := 1000000 })
    [checkEntryPath, opAt, pushAt, wfOp, sizeMatched, atPC, loopState,
    loopAcc, referenceWord, href, hzero, hfalse, hcond, hstack, hcondStack,
    hstackZero, hzeroFalse,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
