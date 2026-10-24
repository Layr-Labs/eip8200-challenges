import Challenge.Modexp.Submission.Proofs.Bytecode.DispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

open EvmSemantics
open EvmSemantics.EVM

set_option maxHeartbeats 5000000 in
set_option linter.unusedSimpArgs false in
theorem run_zeroSetup (input : ByteArray) (hzero : modulusSize input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroSetupPath
      (Main.headerState input) = some (zeroSetupState input) := by
  simp only [zeroSetupState, Main.headerState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hrun : template.halt = .Running := by rw [← htemplate]; rfl
  simp (config := { maxSteps := 200000 })
    [zeroSetupPath, zeroSizePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      hzero, hrun, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]; rfl

set_option linter.unusedSimpArgs false in
theorem run_zeroReturn (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroReturnPath
      (zeroSetupState input) = some (zeroSizeFinalState input) := by
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroWord : UInt256.ofNat 0 = (0 : UInt256) := by decide
  simp only [zeroSetupState, zeroSizeFinalState, Main.headerState]
  generalize htemplate : initialState submissionBytecode input 0 = template
  have hmemory : template.memory = ByteArray.empty := by rw [← htemplate]; rfl
  have hactive : template.activeWords = UInt256.ofNat 0 := by rw [← htemplate]; rfl
  simp [zeroReturnPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hmemory, hactive,
    Challenge.EvmProof.Word.word_toNat_ofNat, h0, hzeroWord]


end Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch

