import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 1196) := by
  have hpc : (initialState submissionBytecode input 0).pc = UInt256.ofNat 0 := rfl
  have hstack : (initialState submissionBytecode input 0).stack = [] := rfl
  have hhalt : (initialState submissionBytecode input 0).halt = .Running := rfl
  have hcode : (initialState submissionBytecode input 0).executionEnv.code
      = submissionBytecode := rfl
  have hpc0 : Artifact.submissionArtifact.instructionPC 0 = 0 := rfl
  have hpc1 : Artifact.submissionArtifact.instructionPC 1 = 3 := rfl
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 0) (b := 3) (by norm_num : 0 + 3 < 2 ^ 256)
  have hdest : (1196 : UInt256).toNat = 1196 := by decide
  have hdestWord : (1196 : UInt256) = UInt256.ofNat 1196 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 1196 = true :=
    Artifact.isValidJumpDest_index 899 (by rfl)
  simp [tramp0Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, hpc, hstack, hhalt, hcode, hpc0, hpc1, hadd, hdest,
    hdestWord, hjump, Challenge.EvmProof.Word.word_toNat_ofNat]


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
