import Challenge.Modexp.Submission.Proofs.Bytecode.ArtifactEarlyWordPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
private theorem run_tramp0_code (code input : ByteArray)
    (hjump : Decode.isValidJumpDest code 5115 = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState code input 0) =
      some { initialState code input 0 with pc := UInt256.ofNat 5115 } := by
  have hzero : (0 : UInt256).toNat = 0 := by decide
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 0) (b := 3) (by norm_num : 0 + 3 < 2 ^ 256)
  have hdest : (5115 : UInt256).toNat = 5115 := by decide
  have hdestWord : (5115 : UInt256) = UInt256.ofNat 5115 := by decide
  simp [tramp0Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, hzero, hadd, hdest, hjump, hdestWord]

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 5115) := by
  exact run_tramp0_code submissionBytecode input Artifact.earlyWordPaths.helperJump


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
