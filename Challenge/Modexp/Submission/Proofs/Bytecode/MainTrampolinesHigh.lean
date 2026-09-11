import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

-- Keep the bytecode-bearing initial state opaque during symbolic execution.
-- Specializing these state-parametric proofs avoids large concrete-state
-- reductions in the kernel without changing any execution theorem.
set_option linter.unusedSimpArgs false in
private theorem run_tramp7_state (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) (hstack : s.stack = []) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      {s with pc := UInt256.ofNat 655} =
      some {s with pc := UInt256.ofNat 1135} := by
  have hsucc699 := Challenge.EvmProof.Word.succ_ofNat
    (n := 655) (by norm_num : 655 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 656) (b := 3) (by norm_num : 656 + 3 < 2 ^ 256)
  have hdest : (1134 : UInt256).toNat = 1134 := by decide
  have hsucc1196 := Challenge.EvmProof.Word.succ_ofNat
    (n := 1134) (by norm_num : 1134 + 1 < 2 ^ 256)
  simp [tramp7Path, opAt, pushAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcode, hrun, hstack,
    hsucc699, hadd, hdest, hsucc1196,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

theorem run_tramp7 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7Path
      (trampolineState input 655) = some (headerEntryState input) :=
  run_tramp7_state (initialState submissionBytecode input 0) rfl rfl rfl

set_option linter.unusedSimpArgs false in
private theorem run_tramp7Jump_state (s : State)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) (hstack : s.stack = []) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      {s with pc := UInt256.ofNat 655} =
      some {s with pc := UInt256.ofNat 1134} := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 655) (by norm_num : 655 + 1 < 2 ^ 256)
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 656) (b := 3) (by norm_num : 656 + 3 < 2 ^ 256)
  have hdest : (1134 : UInt256).toNat = 1134 := by decide
  simp [tramp7JumpPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcode, hrun, hstack, hsucc, hadd, hdest,
    Challenge.EvmProof.Word.word_toNat_ofNat]; rfl

theorem run_tramp7Jump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7JumpPath
      (trampolineState input 655) = some (trampolineState input 1134) :=
  run_tramp7Jump_state (initialState submissionBytecode input 0) rfl rfl rfl

set_option linter.unusedSimpArgs false in
private theorem run_tramp7Dest_state (s : State) (hrun : s.halt = .Running)
    (hstack : s.stack = []) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      {s with pc := UInt256.ofNat 1134} =
      some {s with pc := UInt256.ofNat 1135} := by
  have hsucc := Challenge.EvmProof.Word.succ_ofNat
    (n := 1134) (by norm_num : 1134 + 1 < 2 ^ 256)
  simp [tramp7DestPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hrun, hstack, hsucc,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tramp7Dest (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock tramp7DestPath
      (trampolineState input 1134) = some (headerEntryState input) :=
  run_tramp7Dest_state (initialState submissionBytecode input 0) rfl rfl


end Challenge.Modexp.Submission.Proofs.Bytecode.Main
