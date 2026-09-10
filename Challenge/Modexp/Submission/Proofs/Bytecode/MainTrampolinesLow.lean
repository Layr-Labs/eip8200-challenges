import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
private theorem run_tramp0_code (code input : ByteArray)
    (hjump : Decode.isValidJumpDest code 5283 = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState code input 0) =
      some { initialState code input 0 with pc := UInt256.ofNat 5283 } := by
  have hzero : (0 : UInt256).toNat = 0 := by decide
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 0) (b := 3) (by norm_num : 0 + 3 < 2 ^ 256)
  have hdest : (5283 : UInt256).toNat = 5283 := by decide
  have hdestWord : (5283 : UInt256) = UInt256.ofNat 5283 := by decide
  simp [tramp0Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, hzero, hadd, hdest, hjump, hdestWord]

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 5283) := by
  exact run_tramp0_code submissionBytecode input Artifact.earlyWordPaths.helperJump

set_option linter.unusedSimpArgs false in
theorem run_tramp1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp1Path
      (trampolineState input 14) = some (trampolineState input 52) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 14) (by norm_num : 14 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 14) (b := 3) (by norm_num : 14 + 3 < 2 ^ 256)
  have hdest : (52 : UInt256).toNat = 52 := by decide
  simp [tramp1Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp2Path
      (trampolineState input 52) = some (trampolineState input 98) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 52) (by norm_num : 52 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 53) (b := 3) (by norm_num : 53 + 3 < 2 ^ 256)
  have hdest : (98 : UInt256).toNat = 98 := by decide
  simp [tramp2Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp3 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp3Path
      (trampolineState input 98) = some (trampolineState input 304) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 98) (by norm_num : 98 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 99) (b := 3) (by norm_num : 99 + 3 < 2 ^ 256)
  have hdest : (304 : UInt256).toNat = 304 := by decide
  simp [tramp3Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp4Path
      (trampolineState input 304) = some (trampolineState input 433) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 304) (by norm_num : 304 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 305) (b := 3) (by norm_num : 305 + 3 < 2 ^ 256)
  have hdest : (433 : UInt256).toNat = 433 := by decide
  simp [tramp4Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp5 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp5Path
      (trampolineState input 433) = some (trampolineState input 511) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 433) (by norm_num : 433 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 434) (b := 3) (by norm_num : 434 + 3 < 2 ^ 256)
  have hdest : (511 : UInt256).toNat = 511 := by decide
  simp [tramp5Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp6 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp6Path
      (trampolineState input 511) = some (trampolineState input 694) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 511) (by norm_num : 511 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 512) (b := 3) (by norm_num : 512 + 3 < 2 ^ 256)
  have hdest : (694 : UInt256).toNat = 694 := by decide
  simp [tramp6Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
