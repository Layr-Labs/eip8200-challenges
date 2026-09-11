import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

/-- The jump destination 1134 of trampoline 7, from the artifact's indexed certificate. -/
private theorem tramp7_jumpDest : Decode.isValidJumpDest submissionBytecode 1134 = true := by
  exact Artifact.isValidJumpDest_index 870 (by rfl)

/-! The two trampoline-7 jump certificates are stated over an arbitrary code
array carrying the one jump-destination fact they need, and then instantiated;
this keeps elaboration from evaluating the destination scan on the concrete
bytecode (whose cost grows with the whole runtime size). -/

set_option linter.unusedSimpArgs false in
private theorem run_tramp7_code (code input : ByteArray)
    (hjump : Decode.isValidJumpDest code 1134 = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      { initialState code input 0 with pc := UInt256.ofNat 655 } =
      some { initialState code input 0 with pc := UInt256.ofNat 1135 } := by
  have hsucc699 := Challenge.EvmProof.Word.succ_ofNat
    (n := 655) (by norm_num : 655 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 656) (b := 3) (by norm_num : 656 + 3 < 2 ^ 256)
  have hdest : (1134 : UInt256).toNat = 1134 := by decide
  have hdestWord : (1134 : UInt256) = UInt256.ofNat 1134 := by decide
  have hsucc1196 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1134) (by norm_num : 1134 + 1 < 2 ^ 256)
  simp [tramp7Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, hsucc699, hadd, hdest, hdestWord, hsucc1196, hjump,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tramp7 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      (trampolineState input 655) = some (headerEntryState input) := by
  exact run_tramp7_code submissionBytecode input tramp7_jumpDest

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
  exact run_tramp7Jump_code submissionBytecode input tramp7_jumpDest

set_option linter.unusedSimpArgs false in
theorem run_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      (trampolineState input 1134) = some (headerEntryState input) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 1134) (by norm_num : 1134 + 1 < 2 ^ 256)
  simp [tramp7DestPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, headerEntryState, initialState, hsucc,
    Challenge.EvmProof.Word.word_toNat_ofNat]


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
