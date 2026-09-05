import Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseValue
import Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-! Prepared-input value invariant for the selected complete controller. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
open Challenge.Modexp.Submission.Proofs.Montgomery
open BigBase

theorem exponentState_initial (input : ByteArray) (returnDest : UInt256)
    (rest : List UInt256) (hvalid : ValidInput input)
    (hbig : 32 < modulusSize input)
    (hmodulusPos : 0 < Word.modulusValue input) :
    let b := baseSize input
    let e := exponentSize input
    let m := modulusSize input
    let expOff := Word.expOffset input
    let modOff := Word.modulusOffset input
    let entry := BigComplete.exponentState (Main.headerState input) b e m 96
      expOff modOff returnDest rest
    let M := Word.modulusValue input
    let n := Limbs.limbCount m
    let beta := WordCorrect.baseNat input % M
    let rho := fun x => if M % 2 = 1 then Domain.encode M n x else x
    Limbs.Represents entry.memory 2048 n (rho (1 % M)) ∧
      Limbs.Represents entry.memory 1024 n (rho beta) ∧
      Limbs.Represents entry.memory 0 n M ∧
      (M % 2 = 1 →
        (M * (MachineState.readWord entry.memory 11264).toNat + 1) %
          (2 ^ 256) = 0) := by
  let b := baseSize input
  let e := exponentSize input
  let m := modulusSize input
  let expOff := Word.expOffset input
  let modOff := Word.modulusOffset input
  let M := Word.modulusValue input
  let n := Limbs.limbCount m
  let beta := WordCorrect.baseNat input % M
  let rho := fun x => if M % 2 = 1 then Domain.encode M n x else x
  let header := Main.headerState input
  let loaded := BigComplete.setupState header b e m 96 expOff modOff
    returnDest rest
  let scanTail := BigComplete.scanRest b e m 96 expOff modOff returnDest rest
  let accumulator := BigComplete.modulusOr header b e m 96 expOff modOff
    returnDest rest
  let base := BigComplete.baseState header b e m 96 expOff modOff
    returnDest rest
  let baseTail := BigComplete.baseRest expOff modOff returnDest rest
  let phaseRest := BigComplete.exponentRest modOff returnDest rest
  have hb : b ≤ 1024 := by
    simpa [b] using hvalid.2.1
  have hm : m ≤ 1024 := by
    simpa [m] using hvalid.2.2.2
  have hn : n ≤ 32 := Limbs.limbCount_le_32 m hm
  have hnPos : 0 < n := Limbs.limbCount_pos (by simp [m]; omega)
  have hmodOff : modOff < 2 ^ 256 := by
    rcases hvalid with ⟨_, hb', he', _⟩
    simp only [modOff, Word.modulusOffset, Word.expOffset]
    omega
  have hmodulus : Limbs.Represents loaded.memory 0 n M := by
    have hraw := BigSetup.setupReturned_modulus_represents header b e m 96
      expOff modOff returnDest rest hm hmodOff
    rw [show header.executionEnv.calldata = input by rfl] at hraw
    simpa [loaded, BigComplete.setupState, header, b, e, m, n, M, expOff,
      modOff, Word.modulusValue, Word.modulusOffset] using hraw
  have hzeros := setupReturned_base_buffers_zero header b e m 96 expOff modOff
    returnDest rest hm hmodOff
  have hloadedBaseZero : Limbs.Represents loaded.memory 1024 n 0 := by
    simpa [loaded, BigComplete.setupState, n, m] using hzeros.1
  have hloadedAccZero : Limbs.Represents loaded.memory 2048 n 0 := by
    simpa [loaded, BigComplete.setupState, n, m] using hzeros.2
  have hinitial := baseLoopEntry_initial loaded accumulator n M scanTail
    hnPos hn hloadedBaseZero hloadedAccZero hmodulus
  have hbaseZero : Limbs.Represents base.memory 1024 n 0 := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using hinitial.1
  have hbaseOne : Limbs.Represents base.memory 3072 n 1 := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using hinitial.2.1
  have hbaseZero2048 : Limbs.Represents base.memory 2048 n 0 := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n] using hinitial.2.2.1
  have hbaseModulus : Limbs.Represents base.memory 0 n M := by
    simpa [base, BigComplete.baseState, BigComplete.limbCount, loaded,
      accumulator, scanTail, n, M] using hinitial.2.2.2
  have hreturned := initialAccumulator_represents base accumulator n b e m 96
    baseTail M hnPos hn hmodulusPos hbaseZero hbaseOne hbaseZero2048
    hbaseModulus
  have hbaseEnv : base.executionEnv = header.executionEnv := by
    rfl
  have hvalueEnv := baseValueAfter_executionEnv base header M 96 b hbaseEnv
  have hvalueHeader := baseValueAfter_header_eq input M b (by omega)
  have hvalue : baseValueAfter base M 96 b = beta := by
    rw [hvalueEnv, hvalueHeader]
    rfl
  rw [hvalue] at hreturned
  by_cases hdirect :
      BigComplete.directEligible header b e m 96 expOff modOff returnDest rest
  · have hdirect' :
        n ≠ 0 ∧ n ≤ 32 ∧ b ≤ 32 * n ∧
          (MachineState.readWord loaded.memory 0).toNat % 2 = 1 := by
      simpa [BigComplete.directEligible, BigComplete.setupState,
        BigComplete.limbCount, loaded, n, m] using hdirect
    rcases hdirect' with ⟨hnzero, hnDirect, hbDirect, hoddLoaded⟩
    have hparity := MontgomeryWrapperBlock.modulusLow_parity loaded n M
      hnPos hmodulus
    have hoddM : M % 2 = 1 := by
      omega
    let routed := BigModulus.scanRouted loaded n scanTail
    have hroutedMod : Limbs.Represents routed.memory 0 n M := by
      simpa [routed, BigModulus.scanRouted] using hmodulus
    have hroutedBaseZero : Limbs.Represents routed.memory 1024 n 0 := by
      simpa [routed, BigModulus.scanRouted] using hloadedBaseZero
    have hroutedAccZero : Limbs.Represents routed.memory 2048 n 0 := by
      simpa [routed, BigModulus.scanRouted] using hloadedAccZero
    have hoddRouted :
        (MachineState.readWord routed.memory 0).toNat % 2 = 1 := by
      simpa [routed, BigModulus.scanRouted] using hoddLoaded
    have hfast := MontgomeryFastBaseBlock.fastReturned_correct routed
      accumulator n b (UInt256.ofNat e) (UInt256.ofNat m) 96
      (UInt256.ofNat expOff) phaseRest M hnPos hnDirect hbDirect
      (by omega) hmodulusPos hoddRouted hroutedMod hroutedBaseZero
      hroutedAccZero
    have hselectedDirect :
        BigComplete.selectedReady header b e m 96 expOff modOff returnDest rest =
          MontgomeryFastBaseBlock.fastReturned routed accumulator n b
            (UInt256.ofNat e) (UInt256.ofNat m) 96 (UInt256.ofNat expOff)
            phaseRest := by
      simp only [BigComplete.selectedReady, if_pos hdirect]
      rfl
    have hreadyMod :
        Limbs.Represents
          (BigComplete.selectedReady header b e m 96 expOff modOff
            returnDest rest).memory 0 n M := by
      rw [hselectedDirect]
      exact hfast.1
    have hraw :
        Precompile.bytesToNatPadded routed.executionEnv.calldata 96 b =
          WordCorrect.baseNat input := by
      rfl
    have hreadyBase :
        Limbs.Represents
          (BigComplete.selectedReady header b e m 96 expOff modOff
            returnDest rest).memory 1024 n (WordCorrect.baseNat input) := by
      rw [hselectedDirect]
      simpa [hraw] using hfast.2.1
    have hreadyAcc :
        Limbs.Represents
          (BigComplete.selectedReady header b e m 96 expOff modOff
            returnDest rest).memory 2048 n 0 := by
      rw [hselectedDirect]
      exact hfast.2.2.1
    have hreadyOne :
        Limbs.Represents
          (BigComplete.selectedReady header b e m 96 expOff modOff
            returnDest rest).memory 3072 n 1 := by
      rw [hselectedDirect]
      exact hfast.2.2.2
    have hinit := MontgomeryFastBaseBlock.initialized_correct
      (BigComplete.selectedReady header b e m 96 expOff modOff
        returnDest rest) accumulator n b (UInt256.ofNat e) (UInt256.ofNat m)
      96 (UInt256.ofNat expOff) phaseRest M (WordCorrect.baseNat input)
      hnPos hn hmodulusPos hreadyMod hreadyBase hreadyAcc hreadyOne
    have hinitState :
        Limbs.Represents
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest).memory 2048 n (1 % M) ∧
        Limbs.Represents
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest).memory 1024 n (WordCorrect.baseNat input) ∧
        Limbs.Represents
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest).memory 0 n M := by
      simpa [BigComplete.initializedState, BigComplete.limbCount,
        BigComplete.modulusOr, BigComplete.exponentRest, accumulator, n, m,
        phaseRest] using hinit
    have hsetup := MontgomeryPrepareBlock.setupReturned_correct
      (BigComplete.initializedState header b e m 96 expOff modOff
        returnDest rest) accumulator n
      ([UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
        UInt256.ofNat 96, UInt256.ofNat expOff] ++ phaseRest)
      (WordCorrect.baseNat input) M hn hmodulusPos hinitState.2.2
      hinitState.2.1 hinitState.1
    have hencode :
        Domain.encode M n (WordCorrect.baseNat input) =
          Domain.encode M n beta := by
      simp [Domain.encode, beta, Nat.mul_mod]
    have hexponentDirect :
        BigComplete.exponentState header b e m 96 expOff modOff returnDest rest =
          MontgomeryPrepareBlock.setupReturned
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest)
            accumulator n
            ([UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
              UInt256.ofNat 96, UInt256.ofNat expOff] ++ phaseRest) := by
      simp only [BigComplete.exponentState]
      rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hsetup.2.2.1
    · rw [hexponentDirect]
      change Limbs.Represents
        (BigComplete.exponentState header b e m 96 expOff modOff returnDest rest).memory
          1024 n (rho beta)
      have hbEncoded :
          Limbs.Represents
            (BigComplete.exponentState header b e m 96 expOff modOff returnDest rest).memory
              1024 n (rho (WordCorrect.baseNat input)) := hsetup.2.1
      simpa only [rho, if_pos hoddM, hencode] using hbEncoded
    · rw [hexponentDirect]
      exact hsetup.1
    · rw [hexponentDirect]
      exact hsetup.2.2.2
  · have hinitFallback :
        BigComplete.initializedState header b e m 96 expOff modOff
          returnDest rest =
          BigBaseLoop.initialAccumulator base accumulator n b e m 96
            baseTail := by
      simp only [BigComplete.initializedState, BigComplete.selectedReady,
        if_neg hdirect]
      rfl
    have hinitState :
        Limbs.Represents
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest).memory 2048 n (1 % M) ∧
        Limbs.Represents
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest).memory 1024 n beta ∧
        Limbs.Represents
            (BigComplete.initializedState header b e m 96 expOff modOff
              returnDest rest).memory 0 n M := by
      rw [hinitFallback]
      simpa [BigBaseLoop.initialAccumulator, M, n, beta, hvalue] using hreturned
    have hsetup := MontgomeryPrepareBlock.setupReturned_correct
      (BigComplete.initializedState header b e m 96 expOff modOff
        returnDest rest) accumulator n
      ([UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
        UInt256.ofNat 96, UInt256.ofNat expOff] ++ phaseRest)
      beta M hn hmodulusPos hinitState.2.2 hinitState.2.1 hinitState.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [BigComplete.exponentState, BigComplete.limbCount,
        BigComplete.exponentRest, BigComplete.modulusOr, accumulator, n, m,
        phaseRest, rho] using hsetup.2.2.1
    · simpa [BigComplete.exponentState, BigComplete.limbCount,
        BigComplete.exponentRest, BigComplete.modulusOr, accumulator, n, m,
        phaseRest, rho] using hsetup.2.1
    · simpa [BigComplete.exponentState, BigComplete.limbCount,
        BigComplete.exponentRest, BigComplete.modulusOr, accumulator, n, m,
        phaseRest, rho] using hsetup.1
    · simpa [BigComplete.exponentState, BigComplete.limbCount,
        BigComplete.exponentRest, BigComplete.modulusOr, accumulator, n, m,
        phaseRest, rho] using hsetup.2.2.2

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseCorrect
