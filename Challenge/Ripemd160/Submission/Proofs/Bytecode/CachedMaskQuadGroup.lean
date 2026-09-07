import Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskInline
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityQuadGroup

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace QuadRoundState QuadRoundTemplate
open CavityQuadGroup

def code (q : Params) (shift : Fin 6) : List Instr :=
  CachedMaskInline.template shift q.function.val
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) q.constant

theorem run_left (q : Params) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : q.Fits s) (hstack : rho.length < 1006) (hrun : s.halt = .Running) :
    runInstrSeq (code q 0) (stateAt s pc w (mask :: rho)) =
      some (stateAt s (pcAfter pc (code q 0)) (q.apply s w) (mask :: rho)) := by
  have h := CachedMaskInline.run_left q.function.val q.function.isLt s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    w q.constant rho q.constant_zero hstack hrun
    (q.rotations_bounded 0) (q.rotations_bounded 1)
    (q.rotations_bounded 2) (q.rotations_bounded 3)
  rw [QuadSemantic.quadActiveWordsAfterUInt256_4_eq_of_end_le s
    _ _ _ _ (hfit 0) (hfit 1) (hfit 2) (hfit 3)] at h
  exact h

theorem run_right (q : Params) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hfit : q.Fits s) (hstack : rho.length < 1001) (hrun : s.halt = .Running) :
    runInstrSeq (code q 5) (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho)) =
      some (stateAt s (pcAfter pc (code q 5)) (q.apply s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  have h := CachedMaskInline.run_right q.function.val q.function.isLt s pc
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3)
    w q.constant a b c d e rho q.constant_zero hstack hrun
    (q.rotations_bounded 0) (q.rotations_bounded 1)
    (q.rotations_bounded 2) (q.rotations_bounded 3)
  rw [QuadSemantic.quadActiveWordsAfterUInt256_4_eq_of_end_le s
    _ _ _ _ (hfit 0) (hfit 1) (hfit 2) (hfit 3)] at h
  exact h

theorem advances (q : Params) (shift : Fin 6) :
    ∀ instruction ∈ code q shift, PairMultiplyLift.Advances instruction := by
  exact CachedMaskInline.advances shift q.function.val q.function.isLt
    (q.address 0) (q.address 1) (q.address 2) (q.address 3)
    (q.rotation 0) (q.rotation 1) (q.rotation 2) (q.rotation 3) q.constant

def fourCode (qs : Fin 4 → Params) (shift : Fin 6) : List Instr :=
  code (qs 0) shift ++ code (qs 1) shift ++ code (qs 2) shift ++ code (qs 3) shift

def fourResult (qs : Fin 4 → Params) (s : State) (w : Compression.EvmWorking) :
    Compression.EvmWorking :=
  (qs 3).apply s ((qs 2).apply s ((qs 1).apply s ((qs 0).apply s w)))

/-- Four arbitrary pure quads compose over the exact same preserved frame. -/
theorem run_four (qs : Fin 4 → Params) (shift : Fin 6) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hrun : s.halt = .Running)
    (step : ∀ k nextPC nextWorking,
      runInstrSeq (code (qs k) shift) (stateAt s nextPC nextWorking rho) =
        some (stateAt s (pcAfter nextPC (code (qs k) shift))
          ((qs k).apply s nextWorking) rho)) :
    runInstrSeq (fourCode qs shift) (stateAt s pc w rho) =
      some (stateAt s (pcAfter pc (fourCode qs shift)) (fourResult qs s w) rho) := by
  have hrunAt (nextPC : UInt256) (next : Compression.EvmWorking) :
      (stateAt s nextPC next rho).halt = .Running := by
    simpa [stateAt, roundEntry] using hrun
  have h0 := step 0 pc w
  have h1 := step 1 (pcAfter pc (code (qs 0) shift)) ((qs 0).apply s w)
  have h2 := step 2
    (pcAfter (pcAfter pc (code (qs 0) shift)) (code (qs 1) shift))
    ((qs 1).apply s ((qs 0).apply s w))
  have h3 := step 3
    (pcAfter (pcAfter (pcAfter pc (code (qs 0) shift)) (code (qs 1) shift))
      (code (qs 2) shift))
    ((qs 2).apply s ((qs 1).apply s ((qs 0).apply s w)))
  have hall := QuadRoundState.runInstrSeq_append h0 (hrunAt _ _) <|
    QuadRoundState.runInstrSeq_append h1 (hrunAt _ _) <|
      QuadRoundState.runInstrSeq_append h2 (hrunAt _ _) h3
  simpa only [fourCode, fourResult, QuadRoundState.pcAfter_append,
    List.append_assoc] using hall

theorem run_left_four (qs : Fin 4 → Params) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (rho : List UInt256)
    (hfit : ∀ k, (qs k).Fits s) (hstack : rho.length < 1006)
    (hrun : s.halt = .Running) :
    runInstrSeq (fourCode qs 0) (stateAt s pc w (mask :: rho)) =
      some (stateAt s (pcAfter pc (fourCode qs 0)) (fourResult qs s w) (mask :: rho)) := by
  apply run_four qs 0 s pc w (mask :: rho) hrun
  intro k nextPC next
  exact run_left (qs k) s nextPC next rho (hfit k) hstack hrun

theorem run_right_four (qs : Fin 4 → Params) (s : State) (pc : UInt256)
    (w : Compression.EvmWorking) (a b c d e : UInt256) (rho : List UInt256)
    (hfit : ∀ k, (qs k).Fits s) (hstack : rho.length < 1001)
    (hrun : s.halt = .Running) :
    runInstrSeq (fourCode qs 5) (stateAt s pc w (a :: b :: c :: d :: e :: mask :: rho)) =
      some (stateAt s (pcAfter pc (fourCode qs 5)) (fourResult qs s w)
        (a :: b :: c :: d :: e :: mask :: rho)) := by
  apply run_four qs 5 s pc w (a :: b :: c :: d :: e :: mask :: rho) hrun
  intro k nextPC next
  exact run_right (qs k) s nextPC next a b c d e rho (hfit k) hstack hrun

theorem four_advances (qs : Fin 4 → Params) (shift : Fin 6) :
    ∀ instruction ∈ fourCode qs shift, PairMultiplyLift.Advances instruction := by
  intro instruction hmem
  simp only [fourCode, List.mem_append] at hmem
  rcases hmem with ((h | h) | h) | h
  · exact advances (qs 0) shift instruction h
  · exact advances (qs 1) shift instruction h
  · exact advances (qs 2) shift instruction h
  · exact advances (qs 3) shift instruction h

#print axioms run_left
#print axioms run_right
#print axioms run_left_four
#print axioms run_right_four

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CachedMaskQuadGroup
