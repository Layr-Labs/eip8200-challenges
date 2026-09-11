import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_tramp7 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      (trampolineState input 655) = some (headerEntryState input) := by
  have hsucc699 := Challenge.EvmProof.Word.succ_ofNat
    (n := 655) (by norm_num : 655 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 656) (b := 3) (by norm_num : 656 + 3 < 2 ^ 256)
  have hdest : (1134 : UInt256).toNat = 1134 := by decide
  have hsucc1196 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1134) (by norm_num : 1134 + 1 < 2 ^ 256)
  simp [tramp7Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, headerEntryState, initialState,
    hsucc699, hadd, hdest, hsucc1196,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp7Jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      (trampolineState input 655) = some (trampolineState input 1134) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 655) (by norm_num : 655 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 656) (b := 3) (by norm_num : 656 + 3 < 2 ^ 256)
  have hdest : (1134 : UInt256).toNat = 1134 := by decide
  simp [tramp7JumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

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
