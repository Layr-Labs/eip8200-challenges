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
    (hjump : Decode.isValidJumpDest code 5251 = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState code input 0) =
      some { initialState code input 0 with pc := UInt256.ofNat 5251 } := by
  have hzero : (0 : UInt256).toNat = 0 := by decide
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 0) (b := 3) (by norm_num : 0 + 3 < 2 ^ 256)
  have hdest : (5251 : UInt256).toNat = 5251 := by decide
  have hdestWord : (5251 : UInt256) = UInt256.ofNat 5251 := by decide
  simp [tramp0Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    initialState, hzero, hadd, hdest, hjump, hdestWord]

theorem run_tramp0 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp0Path
      (initialState submissionBytecode input 0) = some (trampolineState input 5251) := by
  exact run_tramp0_code submissionBytecode input Artifact.earlyWordPaths.helperJump

set_option linter.unusedSimpArgs false in
theorem run_tramp1 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp1Path
      (trampolineState input 14) = some (trampolineState input 50) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 14) (by norm_num : 14 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 15) (b := 2) (by norm_num : 15 + 2 < 2 ^ 256)
  have hdest : (50 : UInt256).toNat = 50 := by decide
  simp [tramp1Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp2Path
      (trampolineState input 50) = some (trampolineState input 93) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 50) (by norm_num : 50 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 51) (b := 2) (by norm_num : 51 + 2 < 2 ^ 256)
  have hdest : (93 : UInt256).toNat = 93 := by decide
  simp [tramp2Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp3 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp3Path
      (trampolineState input 93) = some (trampolineState input 294) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 93) (by norm_num : 93 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 94) (b := 3) (by norm_num : 94 + 3 < 2 ^ 256)
  have hdest : (294 : UInt256).toNat = 294 := by decide
  simp [tramp3Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp4 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp4Path
      (trampolineState input 294) = some (trampolineState input 419) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 294) (by norm_num : 294 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 295) (b := 3) (by norm_num : 295 + 3 < 2 ^ 256)
  have hdest : (419 : UInt256).toNat = 419 := by decide
  simp [tramp4Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp5 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp5Path
      (trampolineState input 419) = some (trampolineState input 496) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 419) (by norm_num : 419 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 420) (b := 3) (by norm_num : 420 + 3 < 2 ^ 256)
  have hdest : (496 : UInt256).toNat = 496 := by decide
  simp [tramp5Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp6 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp6Path
      (trampolineState input 496) = some (trampolineState input 655) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 496) (by norm_num : 496 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 497) (b := 3) (by norm_num : 497 + 3 < 2 ^ 256)
  have hdest : (655 : UInt256).toNat = 655 := by decide
  simp [tramp6Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
