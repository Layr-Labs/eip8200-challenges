import Challenge.Modexp.Submission.Proofs.Fast.Guard1024State
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Paths
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace1
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024Logic Guard1024State Guard1024Paths
set_option linter.unusedSimpArgs false in
theorem run_check1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock check1Path (accState input 4373 (acc1 input)) =
      some (accState input 4525 (acc2 input)) := by
  simp [check1Path, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, accState, acc2, chunk1, scanDiff,
    Guard1024Data.checks, initialState, guardPC0, guardPC1,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]
end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace1
