import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardDefs
import Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardLogic

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-! Run theorems for the rsa2048e65537 matcher block. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunFour

open EvmSemantics
open EvmSemantics.EVM
open RsaGuardDefs

private theorem acc_ne (input : ByteArray)
    (h : ¬RsaGuardLogic.MatchesFour input) :
    RsaGuardLogic.guardDiffFour input ≠ 0 := by
  intro hz
  exact h ((RsaGuardLogic.guardDiffFour_eq_zero_iff input).1 hz)

private theorem acc_isZero_zero (input : ByteArray)
    (h : ¬RsaGuardLogic.MatchesFour input) :
    UInt256.isZero (RsaGuardLogic.guardDiffFour input) =
      UInt256.ofNat 0 := by
  have hnat : (RsaGuardLogic.guardDiffFour input).toNat ≠ 0 := by
    intro hz
    apply acc_ne input h
    apply Challenge.EvmProof.Word.word_ext
    rw [show (0 : UInt256).toNat = 0 by decide]
    exact hz
  simp [UInt256.isZero, hnat]

private theorem acc_isZero_one (input : ByteArray)
    (h : RsaGuardLogic.MatchesFour input) :
    UInt256.isZero (RsaGuardLogic.guardDiffFour input) =
      UInt256.ofNat 1 := by
  have h0 : RsaGuardLogic.guardDiffFour input = 0 :=
    (RsaGuardLogic.guardDiffFour_eq_zero_iff input).2 h
  rw [h0]
  decide

set_option linter.unusedSimpArgs false in
theorem run_miss (input : ByteArray) (h : ¬RsaGuardLogic.MatchesFour input) :
    Challenge.EvmProof.Stepper.runLocatedBlock mPathFour
      (Main.trampolineState input 5289) =
      some (Main.trampolineState input 5949) := by
  have hrun : (Main.trampolineState input 5289).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 5289).executionEnv.code =
      submissionBytecode := by rfl
  have hz := acc_isZero_zero input h
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (5949 : UInt256).toNat = 5949 := by decide
  simp (disch := omega) [mPathFour, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_m_rsa2048e65537, jumpHitFour, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
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
theorem run_hit (input : ByteArray) (h : RsaGuardLogic.MatchesFour input) :
    Challenge.EvmProof.Stepper.runLocatedBlock mPathFour
      (Main.trampolineState input 5289) =
      some (Main.trampolineState input 6549) := by
  have hrun : (Main.trampolineState input 5289).halt =
      .Running := by rfl
  have hcode : (Main.trampolineState input 5289).executionEnv.code =
      submissionBytecode := by rfl
  have hz := acc_isZero_one input h
  have hcap0 : (0 : Nat) < 1024 := by omega
  have hcap1 : (1 : Nat) < 1024 := by omega
  have hcap2 : (2 : Nat) < 1024 := by omega
  have hdest : (6549 : UInt256).toNat = 6549 := by decide
  simp (disch := omega) [mPathFour, Main.opAt, Main.pushAt, Main.wfOp,
    pcs_m_rsa2048e65537, jumpHitFour, hz, hdest, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    RsaGuardDefs.entryState, RsaGuardDefs.missState, Main.trampolineState,
    initialState, hrun, hcode, hcap0, hcap1, hcap2,
    UInt256.isTrue, Nat.add_assoc,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.RsaGuardRunFour
