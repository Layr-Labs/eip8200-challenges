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
      (trampolineState input 694) = some (headerEntryState input) := by
  have hsucc699 := Challenge.EvmProof.Word.succ_ofNat
    (n := 694) (by norm_num : 694 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 695) (b := 3) (by norm_num : 695 + 3 < 2 ^ 256)
  have hdest : (1191 : UInt256).toNat = 1191 := by decide
  have hsucc1196 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1191) (by norm_num : 1191 + 1 < 2 ^ 256)
  simp [tramp7Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, headerEntryState, initialState,
    hsucc699, hadd, hdest, hsucc1196,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp7Jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      (trampolineState input 694) = some (trampolineState input 1191) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 694) (by norm_num : 694 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 695) (b := 3) (by norm_num : 695 + 3 < 2 ^ 256)
  have hdest : (1191 : UInt256).toNat = 1191 := by decide
  simp [tramp7JumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, initialState, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

set_option linter.unusedSimpArgs false in
theorem run_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      (trampolineState input 1191) = some (headerEntryState input) := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 1191) (by norm_num : 1191 + 1 < 2 ^ 256)
  simp [tramp7DestPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    trampolineState, headerEntryState, initialState, hsucc,
    Challenge.EvmProof.Word.word_toNat_ofNat]


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
