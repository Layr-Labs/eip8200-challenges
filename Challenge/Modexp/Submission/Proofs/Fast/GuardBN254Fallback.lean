import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254State
import Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Paths

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Fallback

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open GuardBN254State GuardBN254Paths

set_option linter.unusedSimpArgs false in
theorem run_fallback (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPath (branchState input 5179) =
      some (fallbackState input) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 1314 = true :=
    Artifact.isValidJumpDest_index 977 (by rfl)
  simp [fallbackPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fallbackState, Main.trampolineState, branchState, initialState, hjump, guardBN254PC1,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.GuardBN254Fallback
