import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.BigSetup
import Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseLoop
import Challenge.Modexp.Submission.Proofs.Bytecode.BigSerialize
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryFastBaseBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryPrepareBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryDecodeBlock

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSimpArgs false
/-! # Complete certified nonzero multi-limb MODEXP path -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete

open EvmSemantics
open EvmSemantics.EVM
open BigExponent

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

/-! The direct route is the exact fast-block branch predicate. -/
def directEligible (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : Prop :=
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  let n := limbCount m
  n ≠ 0 ∧ n ≤ 32 ∧ b ≤ 32 * n ∧
    (MachineState.readWord loaded.memory 0).toNat % 2 = 1

instance directEligible_decidable (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) :
    Decidable (directEligible s b e m baseOff expOff modOff returnDest rest) := by
  unfold directEligible
  infer_instance

/-! The route output is always the ready state at `pc = 925`. -/
def selectedReady (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let loaded := setupState s b e m baseOff expOff modOff returnDest rest
  let n := limbCount m
  let A := modulusOr s b e m baseOff expOff modOff returnDest rest
  let routed := BigModulus.scanRouted loaded n
    (scanRest b e m baseOff expOff modOff returnDest rest)
  let phaseRest := exponentRest modOff returnDest rest
  if directEligible s b e m baseOff expOff modOff returnDest rest then
    MontgomeryFastBaseBlock.fastReturned routed A n b (UInt256.ofNat e)
      (UInt256.ofNat m) baseOff (UInt256.ofNat expOff) phaseRest
  else
    BigBaseLoop.baseConvertedExit
      (baseState s b e m baseOff expOff modOff returnDest rest)
      A n b e m baseOff
      (baseRest expOff modOff returnDest rest)

def initializedState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let n := limbCount m
  let A := modulusOr s b e m baseOff expOff modOff returnDest rest
  let phaseRest := exponentRest modOff returnDest rest
  MontgomeryFastBaseBlock.initialized
    (selectedReady s b e m baseOff expOff modOff returnDest rest)
    A n b (UInt256.ofNat e) (UInt256.ofNat m) baseOff
    (UInt256.ofNat expOff) phaseRest

def exponentState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let n := limbCount m
  let A := modulusOr s b e m baseOff expOff modOff returnDest rest
  let phaseRest := exponentRest modOff returnDest rest
  MontgomeryPrepareBlock.setupReturned
    (initializedState s b e m baseOff expOff modOff returnDest rest) A n
    ([UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ phaseRest)

def encodedExponentProgressState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let n := limbCount m
  let A := modulusOr s b e m baseOff expOff modOff returnDest rest
  let phaseRest := exponentRest modOff returnDest rest
  BigExponent.exponentPhaseState
    (exponentState s b e m baseOff expOff modOff returnDest rest)
    A n b e m baseOff expOff phaseRest

def exponentProgressState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let n := limbCount m
  let A := modulusOr s b e m baseOff expOff modOff returnDest rest
  let phaseRest := exponentRest modOff returnDest rest
  MontgomeryDecodeBlock.decodeReturned
    (encodedExponentProgressState s b e m baseOff expOff modOff returnDest rest)
    (UInt256.ofNat e) A n
    ([UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ phaseRest)

def completedState (s : State) (b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let accumulator := modulusOr s b e m baseOff expOff modOff returnDest rest
  let progress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  BigSerialize.bigReturned progress accumulator (limbCount m) b e m baseOff
    expOff (exponentRest modOff returnDest rest)

@[simp] theorem bigComplete_baseState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (baseState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  rfl

@[simp] theorem bigComplete_baseState_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (baseState s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  rfl

@[simp] theorem bigComplete_setupState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (setupState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  rfl

@[simp] theorem bigComplete_setupState_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (setupState s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  rfl

@[simp] theorem bigComplete_baseConvertedExit_executionEnv (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff : Nat)
    (rest : List UInt256) :
    (BigBaseLoop.baseConvertedExit s accumulator count baseSize e m baseOff rest).executionEnv =
      s.executionEnv := by
  simp only [BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
    BigBase.baseProgress_executionEnv]

@[simp] theorem bigComplete_baseConvertedExit_halt (s : State)
    (accumulator : UInt256) (count baseSize e m baseOff : Nat)
    (rest : List UInt256) :
    (BigBaseLoop.baseConvertedExit s accumulator count baseSize e m baseOff rest).halt =
      s.halt := by
  simp only [BigBaseLoop.baseConvertedExit, BigBase.outerExit, BigBase.outerLoop,
    BigBase.baseProgress_halt]

@[simp] theorem bigComplete_fastReturned_executionEnv (s : State)
    (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) :
    (MontgomeryFastBaseBlock.fastReturned s A n b eWord mWord baseOff expWord rest).executionEnv =
      s.executionEnv := by
  unfold MontgomeryFastBaseBlock.fastReturned
  split_ifs <;> rfl

@[simp] theorem bigComplete_fastReturned_halt (s : State)
    (A : UInt256) (n b : Nat) (eWord mWord : UInt256)
    (baseOff : Nat) (expWord : UInt256) (rest : List UInt256) :
    (MontgomeryFastBaseBlock.fastReturned s A n b eWord mWord baseOff expWord rest).halt =
      s.halt := by
  unfold MontgomeryFastBaseBlock.fastReturned
  split_ifs <;> rfl

@[simp] theorem bigComplete_scanRouted_executionEnv (s : State)
    (count : Nat) (rest : List UInt256) :
    (BigModulus.scanRouted s count rest).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem bigComplete_scanRouted_halt (s : State)
    (count : Nat) (rest : List UInt256) :
    (BigModulus.scanRouted s count rest).halt = s.halt := by
  rfl

@[simp] theorem selectedReady_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (selectedReady s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  by_cases hd : directEligible s b e m baseOff expOff modOff returnDest rest
  · simp [selectedReady, hd]
  · simp [selectedReady, hd]

@[simp] theorem selectedReady_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (selectedReady s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  by_cases hd : directEligible s b e m baseOff expOff modOff returnDest rest
  · simp [selectedReady, hd]
  · simp [selectedReady, hd]

@[simp] theorem initializedState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (initializedState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  simp only [initializedState, MontgomeryFastBaseBlock.initialized,
    MontgomeryReadyValue.initialize, BigHelpers.addReturned,
    selectedReady_executionEnv]

@[simp] theorem initializedState_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (initializedState s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  simp only [initializedState, MontgomeryFastBaseBlock.initialized,
    MontgomeryReadyValue.initialize, BigHelpers.addReturned,
    selectedReady_halt]

@[simp] theorem exponentState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (exponentState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  simp only [exponentState, MontgomeryPrepareBlock.setupReturned,
    MontgomeryWrapperBlock.returnedState_executionEnv,
    initializedState_executionEnv]

@[simp] theorem exponentState_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (exponentState s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  simp only [exponentState, MontgomeryPrepareBlock.setupReturned,
    MontgomeryWrapperBlock.returnedState_halt, initializedState_halt]

@[simp] theorem encodedExponentProgressState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (encodedExponentProgressState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  simp only [encodedExponentProgressState,
    BigExponent.exponentPhaseState_executionEnv, exponentState_executionEnv]

@[simp] theorem encodedExponentProgressState_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (encodedExponentProgressState s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  simp only [encodedExponentProgressState,
    BigExponent.exponentPhaseState_halt, exponentState_halt]

@[simp] theorem exponentProgressState_executionEnv (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (exponentProgressState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv := by
  simp only [exponentProgressState, MontgomeryDecodeBlock.decodeReturned,
    MontgomeryWrapperBlock.returnedState_executionEnv,
    encodedExponentProgressState_executionEnv]

@[simp] theorem exponentProgressState_halt (s : State)
    (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (exponentProgressState s b e m baseOff expOff modOff returnDest rest).halt =
      s.halt := by
  simp only [exponentProgressState, MontgomeryDecodeBlock.decodeReturned,
    MontgomeryWrapperBlock.returnedState_halt, encodedExponentProgressState_halt]

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
  let phaseRest := exponentRest modOff returnDest rest
  let A := modulusOr s b e m baseOff expOff modOff returnDest rest
  let routed := BigModulus.scanRouted loaded n scanTail
  let ready := selectedReady s b e m baseOff expOff modOff returnDest rest
  let initialized := initializedState s b e m baseOff expOff modOff returnDest rest
  let prepared := exponentState s b e m baseOff expOff modOff returnDest rest
  let encoded := encodedExponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  let progress := exponentProgressState s b e m baseOff expOff modOff
    returnDest rest
  let decodeTail := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ phaseRest
  have hnLe : n ≤ 32 := by
    simpa [n, limbCount] using Limbs.limbCount_le_32 m hmBound
  have hn : n < 2 ^ 256 := by omega
  have hm : m < 2 ^ 256 := by omega
  have hloadedCode : loaded.executionEnv.code = submissionBytecode := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hloadedFork : loaded.fork = .Osaka := by
    change s.fork = .Osaka
    exact hfork
  have hloadedRun : loaded.halt = .Running := by
    change s.halt = .Running
    exact hrun
  have hloadedNp : Precompile.isPrecompileWithConfig
      loaded.executionEnv.precompileConfig loaded.executionEnv.fork
      loaded.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false
    exact hnp
  have hrouteCode : routed.executionEnv.code = submissionBytecode := by
    change loaded.executionEnv.code = submissionBytecode
    exact hloadedCode
  have hrouteFork : routed.fork = .Osaka := by
    change loaded.fork = .Osaka
    exact hloadedFork
  have hrouteRun : routed.halt = .Running := by
    change loaded.halt = .Running
    exact hloadedRun
  have hrouteNp : Precompile.isPrecompileWithConfig
      routed.executionEnv.precompileConfig routed.executionEnv.fork
      routed.executionEnv.codeAddr = false := by
    change Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig
      loaded.executionEnv.fork loaded.executionEnv.codeAddr = false
    exact hloadedNp
  have hsetup := BigSetup.gasSteps_setup s b e m baseOff expOff modOff
    returnDest rest hmBound hmodOff hinputFit (by omega) hcode hfork hrun hnp
  have hscan := BigModulus.gasSteps_scanNonzeroTotal loaded n scanTail
    (by simp [scanTail, scanRest]; omega) hnLe
    (by simpa [A, loaded, modulusOr] using hor)
    hloadedCode hloadedFork hloadedRun hloadedNp
  have hscan' : Challenge.EvmProof.GasSteps
      (setupState s b e m baseOff expOff modOff returnDest rest) routed :=
    Challenge.EvmProof.GasSteps.cast hscan
      (by simp [BigModulus.scanEntry, loaded, scanTail, setupState,
        BigSetup.setupReturned, BigSetup.afterClear6144,
        BigSetup.afterClear2048, BigSetup.afterClear1024,
        BigSetup.afterClear0, BigHelpers.clearReturned,
        BigLoad.loadReturned, BigSetup.saved, scanRest, n, limbCount] ; decide) rfl
  have hroute : Challenge.EvmProof.GasSteps routed ready := by
    have hfast := MontgomeryFastBaseBlock.gasSteps_fastBase routed A n b
      (UInt256.ofNat e) (UInt256.ofNat m) baseOff (UInt256.ofNat expOff)
      phaseRest (by simp [MontgomeryFastBaseBlock.frame, phaseRest, exponentRest]; omega)
      hn hbase hbaseFit hrouteCode hrouteFork hrouteRun hrouteNp
    have hfast' : Challenge.EvmProof.GasSteps routed
        (MontgomeryFastBaseBlock.fastReturned routed A n b
          (UInt256.ofNat e) (UInt256.ofNat m) baseOff (UInt256.ofNat expOff)
          phaseRest) :=
      Challenge.EvmProof.GasSteps.cast hfast
        (by simp [MontgomeryFastBaseBlock.fastEntry,
          MontgomeryFastBaseBlock.fastAt, MontgomeryFastBaseBlock.frame,
          routed, scanTail, phaseRest, exponentRest, scanRest, A, modulusOr,
          limbCount, BigModulus.scanRouted, loaded, n, setupState]) rfl
    by_cases hd : directEligible s b e m baseOff expOff modOff returnDest rest
    · exact Challenge.EvmProof.GasSteps.cast hfast' rfl
        (by simp [ready, selectedReady, hd, routed, loaded, n, scanTail,
          phaseRest, exponentRest, scanRest, modulusOr, A, setupState,
          limbCount])
    · have hfastFallback :
          MontgomeryFastBaseBlock.fastReturned routed A n b
              (UInt256.ofNat e) (UInt256.ofNat m) baseOff
              (UInt256.ofNat expOff) phaseRest =
            BigModulus.scanNonzero loaded n scanTail := by
        by_cases hzero : n = 0
        · have hnzero' : Limbs.limbCount m = 0 := by
            simpa [n, limbCount] using hzero
          simp [MontgomeryFastBaseBlock.fastReturned,
            MontgomeryFastBaseBlock.fastAt, MontgomeryFastBaseBlock.frame,
            hzero, hnzero', routed, scanTail, phaseRest, A,
            BigModulus.scanRouted, BigModulus.scanNonzero, loaded, n,
            modulusOr, setupState, scanRest, exponentRest, limbCount]
        · have hnpos : 1 ≤ n := by omega
          by_cases hlarge : 32 < n
          · have hlarge' : 32 < Limbs.limbCount m := by
              simpa [n, limbCount] using hlarge
            simp [MontgomeryFastBaseBlock.fastReturned,
              MontgomeryFastBaseBlock.fastAt, MontgomeryFastBaseBlock.frame,
              hzero, hlarge, hlarge', routed, scanTail, phaseRest, A,
              BigModulus.scanRouted, BigModulus.scanNonzero, loaded, n,
              modulusOr, setupState, scanRest, exponentRest, limbCount]
          · have hn32 : n ≤ 32 := by omega
            by_cases hwide : 32 * n < b
            · have hwide' : 32 * Limbs.limbCount m < b := by
                simpa [n, limbCount] using hwide
              simp [MontgomeryFastBaseBlock.fastReturned,
                MontgomeryFastBaseBlock.fastAt, MontgomeryFastBaseBlock.frame,
                hzero, hlarge, hwide, hwide', routed, scanTail, phaseRest, A,
                BigModulus.scanRouted, BigModulus.scanNonzero, loaded, n,
                modulusOr, setupState, scanRest, exponentRest, limbCount]
            · have hfit : b ≤ 32 * n := by omega
              have hnzero' : ¬Limbs.limbCount m = 0 := by
                simpa [n, limbCount] using hzero
              have hlarge' : ¬32 < Limbs.limbCount m := by
                simpa [n, limbCount] using hlarge
              have hwide' : ¬32 * Limbs.limbCount m < b := by
                simpa [n, limbCount] using hwide
              by_cases heven :
                  (MachineState.readWord loaded.memory 0).toNat % 2 = 0
              · have ht := BigModulus.scanRouted_loadLowLeaf_zero_eq
                    loaded n scanTail hn32
                    (by simpa [A, loaded, modulusOr] using hor)
                have hevenR :
                    (MachineState.readWord routed.memory 0).toNat % 2 = 0 := by
                  simpa [routed, BigModulus.scanRouted] using heven
                have htR : MontgomeryWrapperBlock.loadLowLeaf routed 0 = routed := ht
                simp only [MontgomeryFastBaseBlock.fastReturned,
                  if_neg hzero, if_neg hlarge, if_neg hwide, if_pos hevenR]
                rw [htR]
                rfl
              · have hodd :
                    (MachineState.readWord loaded.memory 0).toNat % 2 = 1 := by
                  omega
                have hbad : directEligible s b e m baseOff expOff
                    modOff returnDest rest := by
                  simp [directEligible, loaded, n]
                  exact ⟨by omega, hn32, hfit, hodd⟩
                exact (hd hbad).elim
      have hbaseSetup := BigBase.gasSteps_baseSetup loaded A n scanTail
        (by simp [scanTail, scanRest]; omega)
        (by simp only [A, modulusOr, loaded, n]) hn hloadedCode hloadedFork
        hloadedRun hloadedNp
      let hbaseState := baseState s b e m baseOff expOff modOff returnDest rest
      have hbaseCode : hbaseState.executionEnv.code = submissionBytecode := by
        change loaded.executionEnv.code = submissionBytecode
        exact hloadedCode
      have hbaseFork : hbaseState.fork = .Osaka := by
        change loaded.fork = .Osaka
        exact hloadedFork
      have hbaseRun : hbaseState.halt = .Running := by
        change loaded.halt = .Running
        exact hloadedRun
      have hbaseNp : Precompile.isPrecompileWithConfig
          hbaseState.executionEnv.precompileConfig hbaseState.executionEnv.fork
          hbaseState.executionEnv.codeAddr = false := by
        change Precompile.isPrecompileWithConfig loaded.executionEnv.precompileConfig
          loaded.executionEnv.fork loaded.executionEnv.codeAddr = false
        exact hloadedNp
      have hbaseSetup' : Challenge.EvmProof.GasSteps
          (BigModulus.scanNonzero loaded n scanTail) hbaseState :=
        Challenge.EvmProof.GasSteps.cast hbaseSetup rfl
          (by rfl)
      have hbaseReady := BigBaseLoop.gasSteps_baseReady hbaseState A n b e m baseOff
        (baseRest expOff modOff returnDest rest)
        (by simp [baseRest]; omega) hn hbase hbaseFit
        hbaseCode hbaseFork hbaseRun hbaseNp
      have hbaseReady' : Challenge.EvmProof.GasSteps hbaseState
          (BigBaseLoop.baseConvertedExit hbaseState A n b e m baseOff
            (baseRest expOff modOff returnDest rest)) :=
        Challenge.EvmProof.GasSteps.cast hbaseReady
          (by rfl) rfl
      have hbasePath : Challenge.EvmProof.GasSteps
          (MontgomeryFastBaseBlock.fastReturned routed A n b
            (UInt256.ofNat e) (UInt256.ofNat m) baseOff
            (UInt256.ofNat expOff) phaseRest) ready :=
        Challenge.EvmProof.GasSteps.cast
          (hbaseSetup'.trans hbaseReady') hfastFallback.symm
          (by simp [ready, selectedReady, hd, hbaseState, baseState,
            routed, loaded, n, scanTail, phaseRest, exponentRest, scanRest,
            modulusOr, A, setupState, limbCount,
            BigBaseLoop.baseConvertedExit, BigBase.outerExit,
            BigBase.outerLoop, BigBase.baseProgress])
      exact hfast'.trans hbasePath
  have hreadyEntry :
      MontgomeryFastBaseBlock.readyEntry ready A n b (UInt256.ofNat e)
        (UInt256.ofNat m) baseOff (UInt256.ofNat expOff) phaseRest = ready := by
    by_cases hd : directEligible s b e m baseOff expOff modOff returnDest rest
    · have hd' : n ≠ 0 ∧ n ≤ 32 ∧ b ≤ 32 * n ∧
          (MachineState.readWord loaded.memory 0).toNat % 2 = 1 := by
        simpa [directEligible, loaded, n] using hd
      rcases hd' with ⟨hn0, hn32, hfit, hodd⟩
      have hnotlarge : ¬32 < n := by omega
      have hnotwide : ¬32 * n < b := by omega
      have hoddR : (MachineState.readWord routed.memory 0).toNat % 2 = 1 := by
        simpa [routed, BigModulus.scanRouted] using hodd
      have hreadyFast :
          ready = MontgomeryFastBaseBlock.fastReturned routed A n b
            (UInt256.ofNat e) (UInt256.ofNat m) baseOff
            (UInt256.ofNat expOff) phaseRest := by
        simp only [ready, selectedReady, if_pos hd]
        rfl
      have hentry :
          MontgomeryFastBaseBlock.readyEntry
              (MontgomeryFastBaseBlock.fastReturned routed A n b
                (UInt256.ofNat e) (UInt256.ofNat m) baseOff
                (UInt256.ofNat expOff) phaseRest)
              A n b (UInt256.ofNat e) (UInt256.ofNat m) baseOff
                (UInt256.ofNat expOff) phaseRest =
            MontgomeryFastBaseBlock.fastReturned routed A n b
              (UInt256.ofNat e) (UInt256.ofNat m) baseOff
              (UInt256.ofNat expOff) phaseRest := by
        have heven : ¬(MachineState.readWord routed.memory 0).toNat % 2 = 0 := by
          omega
        simp only [MontgomeryFastBaseBlock.fastReturned,
          if_neg hn0, if_neg hnotlarge, if_neg hnotwide, if_neg heven]
        rfl
      rw [hreadyFast]
      exact hentry
    · simp [ready, selectedReady, hd,
        MontgomeryFastBaseBlock.readyEntry,
        MontgomeryFastBaseBlock.readyAt,
        MontgomeryFastBaseBlock.frame, BigBaseLoop.baseConvertedExit,
        BigBase.outerExit, BigBase.outerLoop, BigBase.baseProgress,
        baseState, baseRest, phaseRest, exponentRest, scanRest, limbCount,
        A, n, modulusOr, loaded, setupState, routed, scanTail]
  have hreadyEnv : ready.executionEnv = s.executionEnv := by
    simpa only [ready] using
      (selectedReady_executionEnv s b e m baseOff expOff modOff returnDest rest)
  have hreadyHalt : ready.halt = s.halt := by
    simpa only [ready] using
      (selectedReady_halt s b e m baseOff expOff modOff returnDest rest)
  have hreadyCode : ready.executionEnv.code = submissionBytecode := by
    rw [hreadyEnv]
    exact hcode
  have hreadyFork : ready.fork = .Osaka := by
    change ready.executionEnv.fork = .Osaka
    rw [hreadyEnv]
    exact hfork
  have hreadyRun : ready.halt = .Running := by
    rw [hreadyHalt]
    exact hrun
  have hreadyNp : Precompile.isPrecompileWithConfig
      ready.executionEnv.precompileConfig ready.executionEnv.fork
      ready.executionEnv.codeAddr = false := by
    rw [hreadyEnv]
    exact hnp
  have hinit := MontgomeryFastBaseBlock.gasSteps_initialize ready A n b
    (UInt256.ofNat e) (UInt256.ofNat m) baseOff (UInt256.ofNat expOff)
    phaseRest (by simp [MontgomeryFastBaseBlock.frame, phaseRest, exponentRest]; omega)
    hn hreadyCode hreadyFork hreadyRun hreadyNp
  have hinit' : Challenge.EvmProof.GasSteps ready initialized :=
    Challenge.EvmProof.GasSteps.cast hinit hreadyEntry rfl
  have hinitializedEnv : initialized.executionEnv = s.executionEnv := by
    simpa only [initialized] using
      (initializedState_executionEnv s b e m baseOff expOff modOff returnDest rest)
  have hinitializedHalt : initialized.halt = s.halt := by
    simpa only [initialized] using
      (initializedState_halt s b e m baseOff expOff modOff returnDest rest)
  have hinitializedCode : initialized.executionEnv.code = submissionBytecode := by
    rw [hinitializedEnv]
    exact hcode
  have hinitializedFork : initialized.fork = .Osaka := by
    change initialized.executionEnv.fork = .Osaka
    rw [hinitializedEnv]
    exact hfork
  have hinitializedRun : initialized.halt = .Running := by
    rw [hinitializedHalt]
    exact hrun
  have hinitializedNp : Precompile.isPrecompileWithConfig
      initialized.executionEnv.precompileConfig initialized.executionEnv.fork
      initialized.executionEnv.codeAddr = false := by
    rw [hinitializedEnv]
    exact hnp
  let setupTail := [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ phaseRest
  have hprepare := MontgomeryPrepareBlock.gasSteps_setup initialized A n setupTail
    (by simp [setupTail, phaseRest, exponentRest]; omega) hn hinitializedCode hinitializedFork
    hinitializedRun hinitializedNp
  have hprepareStart : MontgomeryPrepareBlock.setupEntry initialized A n setupTail =
      initialized := by
    rfl
  have hprepare' : Challenge.EvmProof.GasSteps initialized prepared :=
    Challenge.EvmProof.GasSteps.cast hprepare hprepareStart rfl
  have hpreparedEnv : prepared.executionEnv = s.executionEnv := by
    change (exponentState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv
    exact exponentState_executionEnv s b e m baseOff expOff modOff returnDest rest
  have hpreparedHalt : prepared.halt = s.halt := by
    change (exponentState s b e m baseOff expOff modOff returnDest rest).halt = s.halt
    exact exponentState_halt s b e m baseOff expOff modOff returnDest rest
  have hpreparedCode : prepared.executionEnv.code = submissionBytecode := by
    rw [hpreparedEnv]
    exact hcode
  have hpreparedFork : prepared.fork = .Osaka := by
    change prepared.executionEnv.fork = .Osaka
    rw [hpreparedEnv]
    exact hfork
  have hpreparedRun : prepared.halt = .Running := by
    rw [hpreparedHalt]
    exact hrun
  have hpreparedNp : Precompile.isPrecompileWithConfig
      prepared.executionEnv.precompileConfig prepared.executionEnv.fork
      prepared.executionEnv.codeAddr = false := by
    rw [hpreparedEnv]
    exact hnp
  have hphase := BigExponent.gasSteps_exponentPhase prepared A n b e m baseOff
    expOff phaseRest (by simp [phaseRest, exponentRest]; omega) hn hexp hexpFit
    hpreparedCode hpreparedFork hpreparedRun hpreparedNp
  have hphaseStart : BigExponent.exponentEntry prepared A n b e m baseOff
      expOff phaseRest = prepared := by
    rfl
  have hphase' : Challenge.EvmProof.GasSteps prepared
      (BigExponent.coldExit encoded A n b e m baseOff expOff phaseRest) :=
    Challenge.EvmProof.GasSteps.cast hphase hphaseStart rfl
  have hencodedEnv : encoded.executionEnv = s.executionEnv := by
    change (encodedExponentProgressState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv
    exact encodedExponentProgressState_executionEnv s b e m baseOff expOff modOff returnDest rest
  have hencodedHalt : encoded.halt = s.halt := by
    change (encodedExponentProgressState s b e m baseOff expOff modOff returnDest rest).halt = s.halt
    exact encodedExponentProgressState_halt s b e m baseOff expOff modOff returnDest rest
  have hencodedCode : encoded.executionEnv.code = submissionBytecode := by
    rw [hencodedEnv]
    exact hcode
  have hencodedFork : encoded.fork = .Osaka := by
    change encoded.executionEnv.fork = .Osaka
    rw [hencodedEnv]
    exact hfork
  have hencodedRun : encoded.halt = .Running := by
    rw [hencodedHalt]
    exact hrun
  have hencodedNp : Precompile.isPrecompileWithConfig
      encoded.executionEnv.precompileConfig encoded.executionEnv.fork
      encoded.executionEnv.codeAddr = false := by
    rw [hencodedEnv]
    exact hnp
  have hdecode := MontgomeryDecodeBlock.gasSteps_decode encoded
    (UInt256.ofNat e) A n decodeTail
    (by simp [decodeTail, phaseRest, exponentRest]; omega) hn hencodedCode hencodedFork
    hencodedRun hencodedNp
  have hdecodeStart : MontgomeryDecodeBlock.decodeEntry encoded (UInt256.ofNat e)
      A n decodeTail = BigExponent.coldExit encoded A n b e m baseOff expOff
        phaseRest := by
    rfl
  have hdecode' : Challenge.EvmProof.GasSteps
      (BigExponent.coldExit encoded A n b e m baseOff expOff phaseRest) progress :=
    Challenge.EvmProof.GasSteps.cast hdecode hdecodeStart rfl
  have hprogressEnv : progress.executionEnv = s.executionEnv := by
    change (exponentProgressState s b e m baseOff expOff modOff returnDest rest).executionEnv =
      s.executionEnv
    exact exponentProgressState_executionEnv s b e m baseOff expOff modOff returnDest rest
  have hprogressHalt : progress.halt = s.halt := by
    change (exponentProgressState s b e m baseOff expOff modOff returnDest rest).halt = s.halt
    exact exponentProgressState_halt s b e m baseOff expOff modOff returnDest rest
  have hprogressCode : progress.executionEnv.code = submissionBytecode := by
    rw [hprogressEnv]
    exact hcode
  have hprogressFork : progress.fork = .Osaka := by
    change progress.executionEnv.fork = .Osaka
    rw [hprogressEnv]
    exact hfork
  have hprogressRun : progress.halt = .Running := by
    rw [hprogressHalt]
    exact hrun
  have hprogressNp : Precompile.isPrecompileWithConfig
      progress.executionEnv.precompileConfig progress.executionEnv.fork
      progress.executionEnv.codeAddr = false := by
    rw [hprogressEnv]
    exact hnp
  have hserialize := BigSerialize.gasSteps_serializeFromEntry progress A n b e m
    baseOff expOff phaseRest (by simp [phaseRest, exponentRest]; omega) hm hprogressCode
    hprogressFork hprogressRun hprogressNp
  have hserializeStart : BigSerialize.serializerEntry progress A n b e m baseOff
      expOff phaseRest = progress := by
    rfl
  have hserialize' : Challenge.EvmProof.GasSteps progress
      (BigSerialize.bigReturned progress A n b e m baseOff expOff phaseRest) :=
    Challenge.EvmProof.GasSteps.cast hserialize hserializeStart rfl
  exact Challenge.EvmProof.GasSteps.cast
    (hsetup.trans (hscan'.trans (hroute.trans
      (hinit'.trans (hprepare'.trans (hphase'.trans
        (hdecode'.trans hserialize'))))))) rfl
    (by simp [completedState, progress, exponentProgressState, A, n,
      phaseRest, decodeTail])

end Challenge.Modexp.Submission.Proofs.Bytecode.BigComplete
