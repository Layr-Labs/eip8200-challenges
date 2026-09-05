import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardPaths
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardTrace4
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardLogic GuardState GuardPaths
set_option linter.unusedSimpArgs false in
theorem run_check4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock check4Path (accState input 3756 (acc4 input)) =
      some (accState input 3912 (acc5 input)) := by
  simp [check4Path, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, accState, acc5, chunk4, scanDiff,
    GuardData.checks, initialState, guardPC2, guardPC3,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
end Challenge.Modexp.Submission.Proofs.Fast.GuardTrace4
