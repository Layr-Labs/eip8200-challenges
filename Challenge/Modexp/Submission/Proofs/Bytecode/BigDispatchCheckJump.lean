import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
private theorem run_bigCheckJump_code (code input : ByteArray)
    (hjump : Decode.isValidJumpDest code 1187 = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckJumpPath
      { initialState code input 0 with
        pc := UInt256.ofNat 1168
        stack := [1, UInt256.ofNat (96 + (baseSize input + exponentSize input)),
          UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
          UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] } =
      some { initialState code input 0 with
        pc := UInt256.ofNat 1187
        stack := [UInt256.ofNat (96 + (baseSize input + exponentSize input)),
          UInt256.ofNat (96 + baseSize input), UInt256.ofNat (modulusSize input),
          UInt256.ofNat (exponentSize input), UInt256.ofNat (baseSize input)] } := by
  have htrue : UInt256.isTrue 1 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have h1268 : (1187 : UInt256).toNat = 1187 := by decide
  have h1268Word : (1187 : UInt256) = UInt256.ofNat 1187 := by decide
  simp (config := { maxSteps := 50000 })
    [bigCheckJumpPath, pushAt, opAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      initialState, UInt256.isTrue, htrue, h1, h1268,
      h1268Word, hjump,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

theorem run_bigCheckJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckJumpPath
      (bigComparedState input) = some (bigCheckedState input) := by
  exact run_bigCheckJump_code submissionBytecode input jump1268

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
