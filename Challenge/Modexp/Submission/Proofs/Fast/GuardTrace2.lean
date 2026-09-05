import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardPaths
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardTrace2
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardLogic GuardState GuardPaths
set_option linter.unusedSimpArgs false in
theorem run_check2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock check2Path (accState input 3444 (acc2 input)) =
      some (accState input 3600 (acc3 input)) := by
  simp [check2Path, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, accState, acc3, chunk2, scanDiff,
    GuardData.checks, initialState, guardPC1,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
end Challenge.Modexp.Submission.Proofs.Fast.GuardTrace2
