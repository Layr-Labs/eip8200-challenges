import Challenge.Ripemd160.Submission.H39Memo.PatternTraceBase

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.H39Memo.PatternTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof A1000

theorem jump3109 : Decode.isValidJumpDest h39Bytecode 3109 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1106 = 3109 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1106 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3362 : Decode.isValidJumpDest h39Bytecode 3362 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1180 = 3362 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1180 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3431 : Decode.isValidJumpDest h39Bytecode 3431 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1194 = 3431 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1194 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3500 : Decode.isValidJumpDest h39Bytecode 3500 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1208 = 3500 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1208 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3529 : Decode.isValidJumpDest h39Bytecode 3529 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1216 = 3529 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1216 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3599 : Decode.isValidJumpDest h39Bytecode 3599 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1230 = 3599 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1230 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3669 : Decode.isValidJumpDest h39Bytecode 3669 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1244 = 3669 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1244 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3739 : Decode.isValidJumpDest h39Bytecode 3739 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1258 = 3739 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1258 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3768 : Decode.isValidJumpDest h39Bytecode 3768 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1266 = 3768 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1266 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3838 : Decode.isValidJumpDest h39Bytecode 3838 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1280 = 3838 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1280 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3908 : Decode.isValidJumpDest h39Bytecode 3908 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1294 = 3908 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1294 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump3978 : Decode.isValidJumpDest h39Bytecode 3978 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1308 = 3978 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1308 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump4007 : Decode.isValidJumpDest h39Bytecode 4007 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1316 = 4007 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1316 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump4036 : Decode.isValidJumpDest h39Bytecode 4036 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1324 = 4036 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1324 (by rfl)
  simpa only [hp, artifact_code] using hj

theorem jump4107 : Decode.isValidJumpDest h39Bytecode 4107 = true := by
  have hp : Artifact.h39Artifact.instructionPC 1338 = 4107 := by decide
  have hj := Artifact.h39Artifact.isValidJumpDest_index 1338 (by rfl)
  simpa only [hp, artifact_code] using hj

end Challenge.Ripemd160.Submission.H39Memo.PatternTrace

