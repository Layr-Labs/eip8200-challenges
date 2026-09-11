import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
private theorem run_tramp7Jump_code (code input : ByteArray)
    (hjump : Decode.isValidJumpDest code 1134 = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      { initialState code input 0 with pc := UInt256.ofNat 655 } =
      some { initialState code input 0 with pc := UInt256.ofNat 1134 } := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 655) (by norm_num : 655 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 656) (b := 3) (by norm_num : 656 + 3 < 2 ^ 256)
  have hdest : (1134 : UInt256).toNat = 1134 := by decide
  have hdestWord : (1134 : UInt256) = UInt256.ofNat 1134 := by decide
  simp [tramp7JumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, hsucc, hadd, hdest, hdestWord, hjump,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tramp7Jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      (trampolineState input 655) = some (trampolineState input 1134) := by
  exact run_tramp7Jump_code submissionBytecode input jump1196

set_option linter.unusedSimpArgs false in
private theorem run_tramp7Dest_code (code input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      { initialState code input 0 with pc := UInt256.ofNat 1134 } =
      some { initialState code input 0 with pc := UInt256.ofNat 1135 } := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 1134) (by norm_num : 1134 + 1 < 2 ^ 256)
  simp [tramp7DestPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, hsucc, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      (trampolineState input 1134) = some (headerEntryState input) := by
  exact run_tramp7Dest_code submissionBytecode input

theorem run_tramp7 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      (trampolineState input 655) = some (headerEntryState input) := by
  change Challenge.EvmProof.Stepper.runLocatedBlock
    (tramp7JumpPath ++ tramp7DestPath) (trampolineState input 655) = _
  exact Challenge.EvmProof.Stepper.runLocatedBlock_append _ _ _ _ _
    (run_tramp7Jump input) rfl (run_tramp7Dest input)

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
