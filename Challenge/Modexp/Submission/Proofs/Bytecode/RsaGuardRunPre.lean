import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunPre

open EvmSemantics
open EvmSemantics.EVM
open RsaGuardDefs

private theorem msize_read (input : ByteArray) :
    (MachineState.readWord input 64).toNat = modulusSize input := by
  rw [Challenge.EvmProof.Bytes.readWord_toNat]
  rfl

private theorem lit128 : ((128 : UInt256)).toNat = 128 := by decide
private theorem lit256 : ((256 : UInt256)).toNat = 256 := by decide

private theorem eq128_eq (input : ByteArray)
    (h : modulusSize input = 128) :
    UInt256.eq 128 (MachineState.readWord input 64) = UInt256.ofNat 1 := by
  unfold UInt256.eq
  simp [lit128, msize_read input, h]

private theorem eq128_ne (input : ByteArray)
    (h : modulusSize input ≠ 128) :
    UInt256.eq 128 (MachineState.readWord input 64) = UInt256.ofNat 0 := by
  unfold UInt256.eq
  simp [lit128, msize_read input, h]

private theorem eq256_eq (input : ByteArray)
    (h : modulusSize input = 256) :
    UInt256.eq 256 (MachineState.readWord input 64) = UInt256.ofNat 1 := by
  unfold UInt256.eq
  simp [lit256, msize_read input, h]

private theorem eq256_ne (input : ByteArray)
    (h : modulusSize input ≠ 256) :
    UInt256.eq 256 (MachineState.readWord input 64) = UInt256.ofNat 0 := by
  unfold UInt256.eq
  simp [lit256, msize_read input, h]

private theorem lor00 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 0) =
    UInt256.ofNat 0 := by decide
private theorem lor01 : UInt256.lor (UInt256.ofNat 0) (UInt256.ofNat 1) =
    UInt256.ofNat 1 := by decide
private theorem lor10 : UInt256.lor (UInt256.ofNat 1) (UInt256.ofNat 0) =
    UInt256.ofNat 1 := by decide

private theorem flag_taken (input : ByteArray)
    (h128 : modulusSize input ≠ 128) (h256 : modulusSize input ≠ 256) :
    UInt256.isZero (RsaGuardLogic.preFlag input) = UInt256.ofNat 1 := by
  have h0 : RsaGuardLogic.preFlag input = UInt256.ofNat 0 := by
    simp [RsaGuardLogic.preFlag, eq128_ne input h128, eq256_ne input h256, lor00]
  rw [h0]
  decide

private theorem flag_untaken128 (input : ByteArray)
    (h : modulusSize input = 128) :
    UInt256.isZero (RsaGuardLogic.preFlag input) = UInt256.ofNat 0 := by
  have h1 : RsaGuardLogic.preFlag input = UInt256.ofNat 1 := by
    have hne : modulusSize input ≠ 256 := by omega
    simp [RsaGuardLogic.preFlag, eq128_eq input h, eq256_ne input hne, lor10]
  rw [h1]
  decide

private theorem flag_untaken256 (input : ByteArray)
    (h : modulusSize input = 256) :
    UInt256.isZero (RsaGuardLogic.preFlag input) = UInt256.ofNat 0 := by
  have h1 : RsaGuardLogic.preFlag input = UInt256.ofNat 1 := by
    have hne : modulusSize input ≠ 128 := by omega
    simp [RsaGuardLogic.preFlag, eq128_ne input hne, eq256_eq input h, lor01]
  rw [h1]
  decide

set_option linter.unusedSimpArgs false in
theorem run_pre_taken (input : ByteArray) (h128 : modulusSize input ≠ 128) (h256 : modulusSize input ≠ 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock prePath
      (RsaGuardDefs.entryState input) =
      some (Main.trampolineState input 5949) := by
  have hrun : (RsaGuardDefs.entryState input).halt = .Running := by rfl
  have hcode : (RsaGuardDefs.entryState input).executionEnv.code =
      submissionBytecode := by rfl
  have hz := flag_taken input h128 h256
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (5949 : UInt256).toNat = 5949 := by decide
  simp (disch := omega) [prePath, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_guard, jumpMiss, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    RsaGuardDefs.entryState, RsaGuardDefs.missState, Main.trampolineState,
    initialState, hrun, hcode, hcap0, hcap1, hcap2,
    UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_pre_untaken128 (input : ByteArray) (h : modulusSize input = 128) :
    Challenge.EvmProof.Stepper.runLocatedBlock prePath
      (RsaGuardDefs.entryState input) =
      some (Main.trampolineState input 3943) := by
  have hrun : (RsaGuardDefs.entryState input).halt = .Running := by rfl
  have hcode : (RsaGuardDefs.entryState input).executionEnv.code =
      submissionBytecode := by rfl
  have hz := flag_untaken128 input h
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (3943 : UInt256).toNat = 3943 := by decide
  simp (disch := omega) [prePath, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_guard, jumpMiss, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    RsaGuardDefs.entryState, RsaGuardDefs.missState, Main.trampolineState,
    initialState, hrun, hcode, hcap0, hcap1, hcap2,
    UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

set_option linter.unusedSimpArgs false in
theorem run_pre_untaken256 (input : ByteArray) (h : modulusSize input = 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock prePath
      (RsaGuardDefs.entryState input) =
      some (Main.trampolineState input 3943) := by
  have hrun : (RsaGuardDefs.entryState input).halt = .Running := by rfl
  have hcode : (RsaGuardDefs.entryState input).executionEnv.code =
      submissionBytecode := by rfl
  have hz := flag_untaken256 input h
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (3943 : UInt256).toNat = 3943 := by decide
  simp (disch := omega) [prePath, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_guard, jumpMiss, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    RsaGuardDefs.entryState, RsaGuardDefs.missState, Main.trampolineState,
    initialState, hrun, hcode, hcap0, hcap1, hcap2,
    UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_miss (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock missPath
      (Main.trampolineState input 5949) =
      some (RsaGuardDefs.missState input) := by
  have hrun : (Main.trampolineState input
      5949).halt = .Running := by rfl
  have hcode : (Main.trampolineState input
      5949).executionEnv.code = submissionBytecode := by rfl
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (1314 : UInt256).toNat = 1314 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 1314 = true :=
    Artifact.isValidJumpDest_index 977 (by rfl)
  simp (disch := omega) [missPath, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_miss, hjump, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    RsaGuardDefs.entryState, RsaGuardDefs.missState, Main.trampolineState,
    initialState, hrun, hcode, hcap0, hcap1, hcap2,
    UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunPre
