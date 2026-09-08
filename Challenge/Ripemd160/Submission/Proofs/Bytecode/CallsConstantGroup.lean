import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantCache

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantGroup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open CavityQuadGroup

abbrev Params := CavityQuadGroup.Params

def setupCode (constant : UInt256) : List Instr := [push4 constant, swap1]

def keepCode (shift : Fin 6) (j : Fin 3) (q : Params) (constant : UInt256) : List Instr :=
  CallsConstantCache.keepTemplate shift (j.val + 2)
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) constant

def finishCode (shift : Fin 6) (j : Fin 3) (q : Params) (constant : UInt256) : List Instr :=
  CallsConstantCache.finishTemplate shift (j.val + 2)
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) constant

def cachedFourCode (qs : Fin 4 → Params) (j : Fin 3) (constant : UInt256)
    (shift : Fin 6) : List Instr :=
  setupCode constant ++ keepCode shift j (qs 0) constant ++
    keepCode shift j (qs 1) constant ++ keepCode shift j (qs 2) constant ++
    finishCode shift j (qs 3) constant

def cachedFourResult (qs : Fin 4 → Params) (s : State)
    (w : Compression.EvmWorking) : Compression.EvmWorking :=
  (qs 3).apply s ((qs 2).apply s ((qs 1).apply s ((qs 0).apply s w)))

theorem template_eq_code (q : Params) (j : Fin 3) (constant : UInt256)
    (shift : Fin 6) (hfunction : q.function.val = j.val + 2)
    (hconstant : q.constant = constant) :
    CachedMaskHoistInline.template shift (j.val + 2)
        (q.address 0) (q.address 1) (q.address 2) (q.address 3)
        (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) constant =
      CachedMaskQuadGroup.code q shift := by
  unfold CachedMaskQuadGroup.code
  rw [← hfunction, ← hconstant]

theorem run_setup (constant : UInt256) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (frame : List UInt256)
    (hstack : (roundWords w ++ (factor :: frame)).length + 1 < 1024)
    (hrun : s.halt = .Running) :
    runInstrSeq (setupCode constant) (stateAt s pc w frame) =
      some (CallsConstantCache.insertConstant constant
        (stateAt s (pcAfter pc (setupCode constant)) w frame)) := by
  have hstack' : frame.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    simpa [roundWords] using hstack
  have hguard0 : frame.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  have hguard1 := hstack'
  simp (config := { maxSteps := 1000000 }) (discharger := omega)
    [setupCode, push4, swap1, stateAt, roundEntry, runInstrSeq, Stepper.runInstr,
      CallsConstantCache.insertConstant, pcAfter, UInt256.succ, Instr.size,
      List.exchange, List.getElem?_cons_zero, Option.bind_some, hrun, hguard0, hguard1]
  rfl

theorem run_cached_keep_left (j : Fin 3) (q : Params) (constant : UInt256)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking) (rho : List UInt256)
    (hfunction : q.function.val = j.val + 2)
    (hconstant : q.constant = constant) (hfit : q.Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (keepCode 0 j q constant)
        (CallsConstantCache.insertConstant constant (stateAt s pc w (mask :: rho))) =
      some (CallsConstantCache.insertConstant constant
        (stateAt s (pcAfter pc (keepCode 0 j q constant)) (q.apply s w) (mask :: rho))) := by
  have hcache := CallsConstantCache.cache_equiv false false j s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    constant w 0 0 0 0 0 rho hstack hrun
  have hcode := template_eq_code q j constant 0 hfunction hconstant
  have horig := CachedMaskQuadGroup.run_left q s pc w rho hfit hstack hrun
  dsimp [CallsConstantCache.frame] at hcache
  dsimp [CavityQuadGroup.stateAt] at horig
  rw [hcode, horig] at hcache
  simpa [keepCode, CavityQuadGroup.stateAt, roundEntry] using hcache

theorem run_cached_finish_left (j : Fin 3) (q : Params) (constant : UInt256)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking) (rho : List UInt256)
    (hfunction : q.function.val = j.val + 2)
    (hconstant : q.constant = constant) (hfit : q.Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (finishCode 0 j q constant)
        (CallsConstantCache.insertConstant constant (stateAt s pc w (mask :: rho))) =
      some (stateAt s (pcAfter pc (finishCode 0 j q constant)) (q.apply s w)
        (mask :: rho)) := by
  have hcache := CallsConstantCache.cache_equiv false true j s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    constant w 0 0 0 0 0 rho hstack hrun
  have hcode := template_eq_code q j constant 0 hfunction hconstant
  have horig := CachedMaskQuadGroup.run_left q s pc w rho hfit hstack hrun
  dsimp [CallsConstantCache.frame] at hcache
  dsimp [CavityQuadGroup.stateAt] at horig
  rw [hcode, horig] at hcache
  simpa [finishCode, CavityQuadGroup.stateAt, roundEntry] using hcache

theorem run_cached_keep_right (j : Fin 3) (q : Params) (constant : UInt256)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hfunction : q.function.val = j.val + 2)
    (hconstant : q.constant = constant) (hfit : q.Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (keepCode 5 j q constant)
        (CallsConstantCache.insertConstant constant
          (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho))) =
      some (CallsConstantCache.insertConstant constant
        (stateAt s (pcAfter pc (keepCode 5 j q constant)) (q.apply s w)
          (a :: b :: c :: d :: e :: mask :: rho))) := by
  have hcache := CallsConstantCache.cache_equiv true false j s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    constant w a b c d e rho hstack hrun
  have hcode := template_eq_code q j constant 5 hfunction hconstant
  have horig := CachedMaskQuadGroup.run_right q s pc w a b c d e rho hfit hstack hrun
  dsimp [CallsConstantCache.frame] at hcache
  dsimp [CavityQuadGroup.stateAt] at horig
  rw [hcode, horig] at hcache
  simpa [keepCode, CavityQuadGroup.stateAt, roundEntry] using hcache

theorem run_cached_finish_right (j : Fin 3) (q : Params) (constant : UInt256)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hfunction : q.function.val = j.val + 2)
    (hconstant : q.constant = constant) (hfit : q.Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (finishCode 5 j q constant)
        (CallsConstantCache.insertConstant constant
          (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho))) =
      some (stateAt s (pcAfter pc (finishCode 5 j q constant)) (q.apply s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hcache := CallsConstantCache.cache_equiv true true j s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    constant w a b c d e rho hstack hrun
  have hcode := template_eq_code q j constant 5 hfunction hconstant
  have horig := CachedMaskQuadGroup.run_right q s pc w a b c d e rho hfit hstack hrun
  dsimp [CallsConstantCache.frame] at hcache
  dsimp [CavityQuadGroup.stateAt] at horig
  rw [hcode, horig] at hcache
  simpa [finishCode, CavityQuadGroup.stateAt, roundEntry] using hcache

theorem run_cached_four_left (qs : Fin 4 → Params) (j : Fin 3)
    (constant : UInt256) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfunction : ∀ k, (qs k).function.val = j.val + 2)
    (hconstant : ∀ k, (qs k).constant = constant)
    (hfit : ∀ k, (qs k).Fits s)
    (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (cachedFourCode qs j constant 0) (stateAt s pc w (mask :: rho)) =
      some (stateAt s (pcAfter pc (cachedFourCode qs j constant 0))
        (cachedFourResult qs s w) (mask :: rho)) := by
  have hsetupStack :
      (roundWords w ++ (factor :: mask :: rho)).length + 1 < 1024 := by
    simp [roundWords]
    omega
  have hsetup := run_setup constant s pc w (mask :: rho) hsetupStack hrun
  have hrunAt (nextPC : UInt256) (next : Compression.EvmWorking) :
      (CallsConstantCache.insertConstant constant
        (stateAt s nextPC next (mask :: rho))).halt = .Running := by
    simp [CallsConstantCache.insertConstant, CavityQuadGroup.stateAt,
      roundEntry, hrun]
  have h0 := run_cached_keep_left j (qs 0) constant s
    (pcAfter pc (setupCode constant)) w rho
    (hfunction 0) (hconstant 0) (hfit 0) hstack hrun
  have h1 := run_cached_keep_left j (qs 1) constant s
    (pcAfter (pcAfter pc (setupCode constant))
      (keepCode 0 j (qs 0) constant)) ((qs 0).apply s w) rho
    (hfunction 1) (hconstant 1) (hfit 1) hstack hrun
  have h2 := run_cached_keep_left j (qs 2) constant s
    (pcAfter (pcAfter (pcAfter pc (setupCode constant))
        (keepCode 0 j (qs 0) constant))
      (keepCode 0 j (qs 1) constant))
      ((qs 1).apply s ((qs 0).apply s w)) rho
    (hfunction 2) (hconstant 2) (hfit 2) hstack hrun
  have h3 := run_cached_finish_left j (qs 3) constant s
    (pcAfter (pcAfter (pcAfter (pcAfter pc (setupCode constant))
        (keepCode 0 j (qs 0) constant))
      (keepCode 0 j (qs 1) constant))
      (keepCode 0 j (qs 2) constant))
      ((qs 2).apply s ((qs 1).apply s ((qs 0).apply s w))) rho
    (hfunction 3) (hconstant 3) (hfit 3) hstack hrun
  have hkeeps := QuadRoundState.runInstrSeq_append h0
    (hrunAt _ _) <|
    QuadRoundState.runInstrSeq_append h1
      (hrunAt _ _) <|
      QuadRoundState.runInstrSeq_append h2 (hrunAt _ _) h3
  have hall := QuadRoundState.runInstrSeq_append hsetup
    (hrunAt _ _) hkeeps
  simpa only [cachedFourCode, cachedFourResult,
    QuadRoundState.pcAfter_append, List.append_assoc] using hall

theorem run_cached_four_right (qs : Fin 4 → Params) (j : Fin 3)
    (constant : UInt256) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hfunction : ∀ k, (qs k).function.val = j.val + 2)
    (hconstant : ∀ k, (qs k).constant = constant)
    (hfit : ∀ k, (qs k).Fits s)
    (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (cachedFourCode qs j constant 5)
        (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho)) =
      some (stateAt s (pcAfter pc (cachedFourCode qs j constant 5))
        (cachedFourResult qs s w) (a :: b :: c :: d :: e :: mask :: rho)) := by
  have hsetupStack :
      (roundWords w ++ (factor :: a :: b :: c :: d :: e :: mask :: rho)).length + 1 < 1024 := by
    simp [roundWords]
    omega
  have hsetup := run_setup constant s pc w
    (a :: b :: c :: d :: e :: mask :: rho) hsetupStack hrun
  have hrunAt (nextPC : UInt256) (next : Compression.EvmWorking) :
      (CallsConstantCache.insertConstant constant
        (stateAt s nextPC next (a :: b :: c :: d :: e :: mask :: rho))).halt = .Running := by
    simp [CallsConstantCache.insertConstant, CavityQuadGroup.stateAt,
      roundEntry, hrun]
  have h0 := run_cached_keep_right j (qs 0) constant s
    (pcAfter pc (setupCode constant)) w a b c d e rho
    (hfunction 0) (hconstant 0) (hfit 0) hstack hrun
  have h1 := run_cached_keep_right j (qs 1) constant s
    (pcAfter (pcAfter pc (setupCode constant))
      (keepCode 5 j (qs 0) constant)) ((qs 0).apply s w) a b c d e rho
    (hfunction 1) (hconstant 1) (hfit 1) hstack hrun
  have h2 := run_cached_keep_right j (qs 2) constant s
    (pcAfter (pcAfter (pcAfter pc (setupCode constant))
        (keepCode 5 j (qs 0) constant))
      (keepCode 5 j (qs 1) constant))
      ((qs 1).apply s ((qs 0).apply s w)) a b c d e rho
    (hfunction 2) (hconstant 2) (hfit 2) hstack hrun
  have h3 := run_cached_finish_right j (qs 3) constant s
    (pcAfter (pcAfter (pcAfter (pcAfter pc (setupCode constant))
        (keepCode 5 j (qs 0) constant))
      (keepCode 5 j (qs 1) constant))
      (keepCode 5 j (qs 2) constant))
      ((qs 2).apply s ((qs 1).apply s ((qs 0).apply s w))) a b c d e rho
    (hfunction 3) (hconstant 3) (hfit 3) hstack hrun
  have hkeeps := QuadRoundState.runInstrSeq_append h0
    (hrunAt _ _) <|
    QuadRoundState.runInstrSeq_append h1
      (hrunAt _ _) <|
      QuadRoundState.runInstrSeq_append h2 (hrunAt _ _) h3
  have hall := QuadRoundState.runInstrSeq_append hsetup
    (hrunAt _ _) hkeeps
  simpa only [cachedFourCode, cachedFourResult,
    QuadRoundState.pcAfter_append, List.append_assoc] using hall

abbrev run_left_cached_four := run_cached_four_left
abbrev run_right_cached_four := run_cached_four_right

#print axioms template_eq_code
#print axioms run_setup
#print axioms run_cached_keep_left
#print axioms run_cached_finish_left
#print axioms run_cached_keep_right
#print axioms run_cached_finish_right
#print axioms run_cached_four_left
#print axioms run_cached_four_right

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CallsConstantGroup
