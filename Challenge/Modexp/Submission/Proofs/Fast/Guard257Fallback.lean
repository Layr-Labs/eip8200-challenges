import Challenge.Modexp.Submission.Proofs.Fast.Guard257State
import Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Fallback

open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard257State Guard257Paths

set_option linter.unusedSimpArgs false in
theorem run_fallback (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPath (branchState input 4984) =
      some (fallbackState input) := by
  have hjump : Decode.isValidJumpDest submissionBytecode 5032 = true :=
    Artifact.isValidJumpDest_index 2190 (by rfl)
  simp [fallbackPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    fallbackState, Main.trampolineState, branchState, initialState, hjump, guard257PC1,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Fallback
