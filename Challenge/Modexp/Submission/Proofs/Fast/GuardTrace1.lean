import Challenge.Modexp.Submission.Proofs.Fast.GuardState
import Challenge.Modexp.Submission.Proofs.Fast.GuardPaths
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardTrace1
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardLogic GuardState GuardPaths
set_option linter.unusedSimpArgs false in
theorem run_check1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock check1Path (accState input 3292 (acc1 input)) =
      some (accState input 3444 (acc2 input)) := by
  simp [check1Path, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, accState, acc2, chunk1, scanDiff,
    GuardData.checks, initialState, guardPC0, guardPC1,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
end Challenge.Modexp.Submission.Proofs.Fast.GuardTrace1
