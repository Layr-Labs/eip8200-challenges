import Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheTemplates

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheGroups

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open CavityQuadGroup WordCacheTemplates

abbrev words := WordCacheTemplates.words
abbrev cacheWords := words

def setupCode (g : Fin 7) : List Instr :=
  if hasConstant g then CallsConstantGroup.setupCode (constant g) else []

def quadsCode (g : Fin 7) : List Instr :=
  quadCode g 0 ++ quadCode g 1 ++ quadCode g 2 ++ quadCode g 3

def code (g : Fin 7) : List Instr := setupCode g ++ quadsCode g

def result (g : Fin 7) (s : State) (w : Compression.EvmWorking) : Compression.EvmWorking :=
  CachedMaskQuadGroup.fourResult (params g) s w

def left0Code : List Instr := code 0
def left2Code : List Instr := code 1
def left4Code : List Instr := code 2
def right0Code : List Instr := code 3
def right1Code : List Instr := code 4
def right2Code : List Instr := code 5
def right4Code : List Instr := code 6

private theorem entry_halt (g : Fin 7) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hrun : s.halt = .Running) :
    (entry g s pc w a b c d e rho).halt = .Running := by
  cases hc : hasConstant g <;>
    simp [entry, hc, CallsConstantCache.insertConstant, stateAt, roundEntry, hrun]

private theorem afterQuad_keep (g : Fin 7) (k : Fin 4) (hk : k.val ≠ 3)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256) :
    afterQuad g k s pc w a b c d e rho = entry g s pc w a b c d e rho := by
  cases hc : hasConstant g <;> simp [afterQuad, entry, hc, hk]

private theorem afterQuad_finish (g : Fin 7)
    (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256) :
    afterQuad g 3 s pc w a b c d e rho = stateAt s pc w (frame g s a b c d e rho) := by
  simp [afterQuad]

private theorem run_setup (g : Fin 7) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hstack : rho.length < if isRight g then 998 else 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq (setupCode g) (stateAt s pc w (frame g s a b c d e rho)) =
      some (entry g s (pcAfter pc (setupCode g)) w a b c d e rho) := by
  cases hc : hasConstant g
  · simp [setupCode, entry, hc, runInstrSeq, pcAfter]
  · have hrho : rho.length < 1003 := by split_ifs at hstack <;> omega
    have hframe : (frame g s a b c d e rho).length ≤ rho.length + 9 := by
      unfold frame
      split <;> simp [WordCacheTemplates.words] <;> omega
    have hcap : (roundWords w ++ (factor :: frame g s a b c d e rho)).length + 1 < 1024 := by
      simp only [roundWords, List.length_append, List.length_cons, List.length_nil]
      omega
    simpa [setupCode, entry, hc] using
      CallsConstantGroup.run_setup (constant g) s pc w (frame g s a b c d e rho) hcap hrun

private theorem run_quads (g : Fin 7) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < if isRight g then 998 else 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq (quadsCode g) (entry g s pc w a b c d e rho) =
      some (stateAt s (pcAfter pc (quadsCode g)) (result g s w) (frame g s a b c d e rho)) := by
  have h0 := run_quad g 0 s pc w a b c d e rho hactive hstack hrun
  rw [afterQuad_keep g 0 (by decide)] at h0
  have h1 := run_quad g 1 s (pcAfter pc (quadCode g 0))
    ((params g 0).apply s w) a b c d e rho hactive hstack hrun
  rw [afterQuad_keep g 1 (by decide)] at h1
  have h2 := run_quad g 2 s (pcAfter (pcAfter pc (quadCode g 0)) (quadCode g 1))
    ((params g 1).apply s ((params g 0).apply s w)) a b c d e rho hactive hstack hrun
  rw [afterQuad_keep g 2 (by decide)] at h2
  have h3 := run_quad g 3 s
    (pcAfter (pcAfter (pcAfter pc (quadCode g 0)) (quadCode g 1)) (quadCode g 2))
    ((params g 2).apply s ((params g 1).apply s ((params g 0).apply s w)))
    a b c d e rho hactive hstack hrun
  rw [afterQuad_finish] at h3
  have hrunAt (nextPC : UInt256) (next : Compression.EvmWorking) :
      (entry g s nextPC next a b c d e rho).halt = .Running :=
    entry_halt g s nextPC next a b c d e rho hrun
  have hall := QuadRoundState.runInstrSeq_append h0 (hrunAt _ _) <|
    QuadRoundState.runInstrSeq_append h1 (hrunAt _ _) <|
      QuadRoundState.runInstrSeq_append h2 (hrunAt _ _) h3
  simpa only [quadsCode, result, CachedMaskQuadGroup.fourResult,
    QuadRoundState.pcAfter_append, List.append_assoc] using hall

theorem run_code (g : Fin 7) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat)
    (hstack : rho.length < if isRight g then 998 else 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq (code g) (stateAt s pc w (frame g s a b c d e rho)) =
      some (stateAt s (pcAfter pc (code g)) (result g s w) (frame g s a b c d e rho)) := by
  have hsetup := run_setup g s pc w a b c d e rho hstack hrun
  have hquads := run_quads g s (pcAfter pc (setupCode g)) w a b c d e rho hactive hstack hrun
  have hall := QuadRoundState.runInstrSeq_append hsetup
    (entry_halt g s (pcAfter pc (setupCode g)) w a b c d e rho hrun) hquads
  simpa only [code, QuadRoundState.pcAfter_append] using hall

theorem run_left0 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq left0Code (stateAt s pc w (mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc left0Code) (CachedMaskQuadGroup.fourResult (CachedMaskParams.left 0) s w)
        (mask :: (words s ++ rho))) := by
  simpa [code, left0Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 0 s pc w 0 0 0 0 0 rho hactive hstack hrun

#print axioms run_left0

theorem run_left2 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq left2Code (stateAt s pc w (mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc left2Code) (CallsConstantGroup.cachedFourResult CallsConstantParams.left2 s w)
        (mask :: (words s ++ rho))) := by
  simpa [code, left2Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 1 s pc w 0 0 0 0 0 rho hactive hstack hrun

#print axioms run_left2

theorem run_left4 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 1003)
    (hrun : s.halt = .Running) :
    runInstrSeq left4Code (stateAt s pc w (mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc left4Code) (CallsConstantGroup.cachedFourResult CallsConstantParams.left4 s w)
        (mask :: (words s ++ rho))) := by
  simpa [code, left4Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 2 s pc w 0 0 0 0 0 rho hactive hstack hrun

#print axioms run_left4

theorem run_right0 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 998)
    (hrun : s.halt = .Running) :
    runInstrSeq right0Code (stateAt s pc w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc right0Code) (CallsConstantGroup.cachedFourResult CallsConstantParams.right0 s w)
        (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  simpa [code, right0Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 3 s pc w a b c d e rho hactive hstack hrun

#print axioms run_right0

theorem run_right1 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 998)
    (hrun : s.halt = .Running) :
    runInstrSeq right1Code (stateAt s pc w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc right1Code) (CallsConstantGroup.cachedFourResult CallsConstantParams.right1 s w)
        (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  simpa [code, right1Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 4 s pc w a b c d e rho hactive hstack hrun

#print axioms run_right1

theorem run_right2 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 998)
    (hrun : s.halt = .Running) :
    runInstrSeq right2Code (stateAt s pc w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc right2Code) (CallsConstantGroup.cachedFourResult CallsConstantParams.right2 s w)
        (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  simpa [code, right2Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 5 s pc w a b c d e rho hactive hstack hrun

#print axioms run_right2

theorem run_right4 (s : State) (pc : UInt256) (w : Compression.EvmWorking)
    (a b c d e : UInt256) (rho : List UInt256)
    (hactive : 11 ≤ s.activeWords.toNat) (hstack : rho.length < 998)
    (hrun : s.halt = .Running) :
    runInstrSeq right4Code (stateAt s pc w (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) =
      some (stateAt s (pcAfter pc right4Code) (CachedMaskQuadGroup.fourResult CachedMaskParams.right s w)
        (a :: b :: c :: d :: e :: mask :: (words s ++ rho))) := by
  simpa [code, right4Code, result, params, isRight, frame, words,
    CachedMaskQuadGroup.fourResult, CallsConstantGroup.cachedFourResult] using
    run_code 6 s pc w a b c d e rho hactive hstack hrun

#print axioms run_right4

#print axioms run_code

end Challenge.Ripemd160.Submission.Proofs.Bytecode.WordCacheGroups
