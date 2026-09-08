import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-! Run theorems for the rsa1024e65537 matcher block. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunTwo

open EvmSemantics
open EvmSemantics.EVM
open RsaGuardDefs

private theorem acc_ne (input : ByteArray)
    (h : ¬RsaGuardLogic.MatchesTwo input) :
    RsaGuardLogic.guardDiffTwo input ≠ 0 := by
  intro hz
  exact h ((RsaGuardLogic.guardDiffTwo_eq_zero_iff input).1 hz)

private theorem acc_isZero_zero (input : ByteArray)
    (h : ¬RsaGuardLogic.MatchesTwo input) :
    UInt256.isZero (RsaGuardLogic.guardDiffTwo input) =
      UInt256.ofNat 0 := by
  have hnat : (RsaGuardLogic.guardDiffTwo input).toNat ≠ 0 := by
    intro hz
    apply acc_ne input h
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

private theorem acc_isZero_one (input : ByteArray)
    (h : RsaGuardLogic.MatchesTwo input) :
    UInt256.isZero (RsaGuardLogic.guardDiffTwo input) =
      UInt256.ofNat 1 := by
  have h0 : RsaGuardLogic.guardDiffTwo input = 0 :=
    (RsaGuardLogic.guardDiffTwo_eq_zero_iff input).2 h
  rw [h0]
  decide

set_option linter.unusedSimpArgs false in
theorem run_miss (input : ByteArray) (h : ¬RsaGuardLogic.MatchesTwo input) :
    Challenge.EvmProof.Stepper.runLocatedBlock mPathTwo
      (Main.trampolineState input 4286) =
      some (Main.trampolineState input 4631) := by
  have hrun : (Main.trampolineState input 4286).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 4286).executionEnv.code =
      submissionBytecode := by rfl
  have hz := acc_isZero_zero input h
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (4631 : UInt256).toNat = 4631 := by decide
  simp (disch := omega) [mPathTwo, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_m_rsa1024e65537, jumpHitTwo, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
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
theorem run_hit (input : ByteArray) (h : RsaGuardLogic.MatchesTwo input) :
    Challenge.EvmProof.Stepper.runLocatedBlock mPathTwo
      (Main.trampolineState input 4286) =
      some (Main.trampolineState input 6104) := by
  have hrun : (Main.trampolineState input 4286).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 4286).executionEnv.code =
      submissionBytecode := by rfl
  have hz := acc_isZero_one input h
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (6104 : UInt256).toNat = 6104 := by decide
  simp (disch := omega) [mPathTwo, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_m_rsa1024e65537, jumpHitTwo, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    RsaGuardDefs.entryState, RsaGuardDefs.missState, Main.trampolineState,
    initialState, hrun, hcode, hcap0, hcap1, hcap2,
    UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunTwo
