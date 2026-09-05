import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardPaths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Fast.GuardTrace0

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardLogic GuardState GuardPaths

set_option linter.unusedSimpArgs false in
theorem run_prelude (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock preludePath (entryState input) =
      some (accState input 3141 (acc0 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [preludePath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    entryState, Main.trampolineState, accState, acc0, initialState, guardPC0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

set_option linter.unusedSimpArgs false in
theorem run_check0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock check0Path (accState input 3141 (acc0 input)) =
      some (accState input 3292 (acc1 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [check0Path, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, acc1, GuardState.chunk0, scanDiff, GuardData.checks, initialState, guardPC0,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

end Challenge.Modexp.Submission.Proofs.Fast.GuardTrace0
