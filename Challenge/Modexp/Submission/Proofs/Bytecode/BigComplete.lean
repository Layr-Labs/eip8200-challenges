import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.BigSetup
import Challenge.Modexp.Submission.Proofs.Bytecode.BigSerialize
import Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseDirect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Complete certified nonzero multi-limb MODEXP path -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete

open EvmSemantics
open EvmSemantics.EVM

open BigExponent

private instance eligibleDecidable (s : State) (b m baseOff modOff : Nat) :
    Decidable (BigBaseDirect.Eligible s b m baseOff modOff) := by
  unfold BigBaseDirect.Eligible
  infer_instance

def scanRest (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff, UInt256.ofNat modOff,
    returnDest] ++ rest

def baseRest (expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat expOff, UInt256.ofNat modOff, returnDest] ++ rest

def exponentRest (modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat modOff, returnDest] ++ rest

def setupState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  BigSetup.setupReturned s b e m baseOff expOff modOff returnDest rest

def limbCount (m : Nat) : Nat := Limbs.limbCount m

def modulusOr (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : UInt256 :=
  BigModulus.scanOr
    (setupState s b e m baseOff expOff modOff returnDest rest).memory
    (limbCount m)

def baseState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  BigBase.baseLoopEntry loaded
    (modulusOr s b e m baseOff expOff modOff returnDest rest) (limbCount m)
    (scanRest b e m baseOff expOff modOff returnDest rest)

def exponentState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  if BigBaseDirect.Eligible loaded b m baseOff modOff then
    BigBaseDirect.directInitialAccumulator loaded accumulator (limbCount m)
      b e m baseOff expOff modOff returnDest rest
  else
    let base := baseState s b e m baseOff expOff modOff returnDest rest
    BigBaseLoop.initialAccumulator base accumulator (limbCount m) b e m baseOff
      (baseRest expOff modOff returnDest rest)

@[simp] theorem exponentState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (exponentState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let base := baseState s b e m baseOff expOff modOff returnDest rest
  let baseTail := baseRest expOff modOff returnDest rest
  have hentry : exponentState s b e m baseOff expOff modOff returnDest rest =
      if BigBaseDirect.Eligible loaded b m baseOff modOff then
        BigBaseDirect.directInitialAccumulator loaded accumulator (limbCount m)
          b e m baseOff expOff modOff returnDest rest
      else
        BigBaseLoop.initialAccumulator base accumulator (limbCount m) b e m
          baseOff baseTail := by
    rfl
  by_cases heligible : BigBaseDirect.Eligible loaded b m baseOff modOff
  · rw [hentry, if_pos heligible]
    rfl
  · rw [hentry, if_neg heligible]
    simp [base,
      BigBaseLoop.initialAccumulator, BigBaseLoop.baseConvertedExit,
      BigBase.outerExit, BigBase.outerLoop, BigHelpers.addReturned,
      baseState, BigBase.baseLoopEntry, BigBase.afterClearDouble,
      BigHelpers.clearReturned, BigModulus.scanNonzero, setupState,
      BigSetup.setupReturned, BigLoad.loadReturned, BigLoad.loadLoop,
      BigSetup.afterClear6144, BigSetup.afterClear2048,
      BigSetup.afterClear1024, BigSetup.afterClear0]

def exponentProgressState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let entry := exponentState s b e m baseOff expOff modOff returnDest rest
  BigExponent.exponentPhaseState entry accumulator (limbCount m) b e m
    baseOff expOff (exponentRest modOff returnDest rest)

def completedState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let progress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  BigSerialize.bigReturned progress accumulator (limbCount m) b e m baseOff
    expOff (exponentRest modOff returnDest rest)

def gasSteps_nonzero (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hmBound : m ≤ 1024) (hmodOff : modOff < 2 ^ 256)
    (hinputFit : modOff + m ≤ 2 ^ 256) (hbase : b < 2 ^ 256)
    (hbaseFit : baseOff + b < 2 ^ 256) (hexp : e < 2 ^ 256)
    (hexpFit : expOff + e < 2 ^ 256) (hcap : rest.length < 960)
    (hor : modulusOr s b e m baseOff expOff modOff returnDest rest ≠ 0)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigSetup.setupEntry s b e m baseOff expOff modOff returnDest rest)
      (completedState s b e m baseOff expOff modOff returnDest rest) := by
  let n := limbCount m
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  let scanTail := scanRest b e m baseOff expOff modOff returnDest rest
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let baseTail := baseRest expOff modOff returnDest rest
  let expTail := exponentRest modOff returnDest rest
  let base := baseState s b e m baseOff expOff modOff returnDest rest
  let expEntry := exponentState s b e m baseOff expOff modOff returnDest rest
  let expProgress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  have hnLe : n ≤ 32 := Limbs.limbCount_le_32 m hmBound
  have hn : n < 2 ^ 256 := by omega
  have hExpEntry : expEntry =
      if BigBaseDirect.Eligible loaded b m baseOff modOff then
        BigBaseDirect.directInitialAccumulator loaded accumulator n b e m
          baseOff expOff modOff returnDest rest
      else
        BigBaseLoop.initialAccumulator base accumulator n b e m baseOff
          baseTail := by
    rfl
  have hsetup := BigSetup.gasSteps_setup s b e m baseOff expOff modOff
    returnDest rest hmBound hmodOff hinputFit (by omega) hcode hfork hrun hnp
  have hscan := BigModulus.gasSteps_scanNonzeroTotal loaded n scanTail
    (by simp [scanTail, scanRest]; omega) hnLe hor
    (by change s.executionEnv.code = submissionBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have hbaseSetup := BigBase.gasSteps_baseSetup loaded accumulator n scanTail
    (by simp [scanTail, scanRest]; omega) rfl hn
    (by change s.executionEnv.code = submissionBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have hconversion := BigBaseLoop.gasSteps_baseConversion base accumulator n b e
    m baseOff baseTail (by simp [baseTail, baseRest]; omega) hn hbase hbaseFit
    (by change s.executionEnv.code = submissionBytecode; exact hcode)
    (by change s.fork = .Osaka; exact hfork)
    (by change s.halt = .Running; exact hrun)
    (by
      change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
        s.executionEnv.codeAddr = false
      exact hnp)
  have hbasePhase : Challenge.EvmProof.GasSteps
      (BigBase.afterClearDouble loaded accumulator n scanTail) expEntry := by
    by_cases heligible : BigBaseDirect.Eligible loaded b m baseOff modOff
    · have hdirect := BigBaseDirect.gasSteps_eligible loaded accumulator n b e m
        baseOff expOff modOff returnDest rest
        (by omega) hn hbase (by omega) (by omega) (by omega) (by omega)
        heligible
        (by change s.executionEnv.code = submissionBytecode; exact hcode)
        (by change s.fork = .Osaka; exact hfork)
        (by change s.halt = .Running; exact hrun)
        (by
          change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
            s.executionEnv.fork s.executionEnv.codeAddr = false
          exact hnp)
      exact Challenge.EvmProof.GasSteps.cast hdirect
        (by simp [scanTail, scanRest, BigBaseDirect.fullRest])
        (by rw [hExpEntry, if_pos heligible])
    · have hfallback := BigBaseDirect.gasSteps_ineligible loaded accumulator n b
        e m baseOff expOff modOff returnDest rest (by omega) hbase (by omega)
        (by omega) (by omega) heligible
        (by change s.executionEnv.code = submissionBytecode; exact hcode)
        (by change s.fork = .Osaka; exact hfork)
        (by change s.halt = .Running; exact hrun)
        (by
          change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
            s.executionEnv.fork s.executionEnv.codeAddr = false
          exact hnp)
      exact Challenge.EvmProof.GasSteps.cast (hfallback.trans hconversion)
        (by simp [scanTail, scanRest, BigBaseDirect.fullRest])
        (by rw [hExpEntry, if_neg heligible])
  have hExpEnv : expEntry.executionEnv = s.executionEnv := by
    by_cases heligible : BigBaseDirect.Eligible loaded b m baseOff modOff
    · rw [hExpEntry, if_pos heligible]
      rfl
    · rw [hExpEntry, if_neg heligible]
      simp [BigBaseLoop.initialAccumulator, BigBaseLoop.baseConvertedExit,
        BigBase.outerExit, BigBase.outerLoop, BigHelpers.addReturned,
        base, baseState, BigBase.baseLoopEntry, BigBase.afterClearDouble,
        BigHelpers.clearReturned, BigModulus.scanNonzero, loaded, setupState,
        BigSetup.setupReturned, BigSetup.afterClear6144,
        BigSetup.afterClear2048, BigSetup.afterClear1024, BigSetup.afterClear0,
        BigLoad.loadReturned, BigLoad.loadLoop]
  have hExpHalt : expEntry.halt = s.halt := by
    by_cases heligible : BigBaseDirect.Eligible loaded b m baseOff modOff
    · rw [hExpEntry, if_pos heligible]
      rfl
    · rw [hExpEntry, if_neg heligible]
      simp [BigBaseLoop.initialAccumulator, BigBaseLoop.baseConvertedExit,
        BigBase.outerExit, BigBase.outerLoop, BigHelpers.addReturned,
        base, baseState, BigBase.baseLoopEntry, BigBase.afterClearDouble,
        BigHelpers.clearReturned, BigModulus.scanNonzero, loaded, setupState,
        BigSetup.setupReturned, BigSetup.afterClear6144,
        BigSetup.afterClear2048, BigSetup.afterClear1024, BigSetup.afterClear0,
        BigLoad.loadReturned, BigLoad.loadLoop]
  have hProgressEnv : expProgress.executionEnv = s.executionEnv := by
    rw [show expProgress = BigExponent.exponentPhaseState expEntry accumulator
      n b e m baseOff expOff expTail by rfl]
    rw [BigExponent.exponentPhaseState_executionEnv]
    exact hExpEnv
  have hProgressHalt : expProgress.halt = s.halt := by
    rw [show expProgress = BigExponent.exponentPhaseState expEntry accumulator
      n b e m baseOff expOff expTail by rfl]
    rw [BigExponent.exponentPhaseState_halt]
    exact hExpHalt
  have hphase := BigExponent.gasSteps_exponentPhase expEntry accumulator n b e
    m baseOff expOff expTail (by simp [expTail, exponentRest]; omega) hn hexp
    hexpFit
    (by rw [hExpEnv]; exact hcode)
    (by change expEntry.executionEnv.fork = .Osaka; rw [hExpEnv]; exact hfork)
    (by rw [hExpHalt]; exact hrun)
    (by
      rw [hExpEnv]
      exact hnp)
  have hphaseEntry :
      BigExponent.exponentEntry expEntry accumulator n b e m baseOff expOff
          expTail = expEntry := by
    by_cases heligible : BigBaseDirect.Eligible loaded b m baseOff modOff
    · rw [hExpEntry, if_pos heligible]
      rfl
    · rw [hExpEntry, if_neg heligible]
      rfl
  have hphase' := Challenge.EvmProof.GasSteps.cast hphase hphaseEntry rfl
  have hserialize := BigSerialize.gasSteps_serializeFromEntry expProgress accumulator
    n b e m baseOff expOff expTail (by simp [expTail, exponentRest]; omega)
    (by omega)
    (by rw [hProgressEnv]; exact hcode)
    (by change expProgress.executionEnv.fork = .Osaka
        rw [hProgressEnv]
        exact hfork)
    (by rw [hProgressHalt]; exact hrun)
    (by
      rw [hProgressEnv]
      exact hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (hsetup.trans (hscan.trans (hbaseSetup.trans
      (hbasePhase.trans (hphase'.trans hserialize)))))
    rfl
    (by simp [completedState, expProgress, exponentProgressState, accumulator,
      n, expTail])


end Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete
