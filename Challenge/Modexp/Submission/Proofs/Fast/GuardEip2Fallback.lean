import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2State
import Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Paths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Fallback

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardEip2State GuardEip2Paths

set_option linter.unusedSimpArgs false in
theorem run_fallback (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPath (branchState input 4974) =
      some (fallbackState input) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1314 = true :=
    Artifact.isValidJumpDest_index 977 (by rfl)
  simp [fallbackPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fallbackState, Main.trampolineState, branchState, initialState, hjump, gEip2PC0, gEip2PC1, gEip2PC2,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.GuardEip2Fallback
