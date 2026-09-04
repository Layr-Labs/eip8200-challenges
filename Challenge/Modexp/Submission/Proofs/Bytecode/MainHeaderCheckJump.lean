import Challenge.Modexp.Submission.Proofs.Bytecode.MainHeaderFinishDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerCheckJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerCheckJumpPath
      (headerCheckPassedState input) = some (headerState input) := by
  have htrue : UInt256.isTrue 1 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have ha1223 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1229) (b := 3) (by norm_num : 1229 + 3 < 2 ^ 256)
  have hdest : (1234 : UInt256).toNat = 1234 := by decide
  have hdestWord : (1234 : UInt256) = UInt256.ofNat 1234 := by decide
  simp (config := { maxSteps := 40000 })
    [headerCheckJumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerCheckPassedState, headerState, initialState, UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat, htrue, h1, ha1223, hdest,
    hdestWord]

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
