import Challenge.Modexp.Submission.Proofs.Fast.SquareDiag
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SgtStep

noncomputable section
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

/-! Submission-local signed comparison evaluator. Unlike tests, its soundness is
proved against the pinned StepRunning.sgt rule for all input states. -/
namespace CycleSubmission.Global.Fast.SignedTopBit
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
attribute [local instance] Classical.propDecidable
open Challenge.EvmProof Challenge.EvmProof.Stepper
open Challenge.Modexp.Submission.Proofs.Fast

/-- The signed comparison against zero is exactly the top bit, for every word. -/
theorem sgt_zero_eq_shr (x : UInt256) :
    UInt256.sgt (UInt256.ofNat 0) x = UInt256.shiftRight x (UInt256.ofNat 255) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [SquareDiag.sgt_zero_toNat, Challenge.EvmProof.Word.shiftRight_toNat x (by decide)]
  exact (Nat.shiftRight_eq_div_pow x.toNat 255).symm

def runInstrS (instruction : Instr) (s : State) : Option State :=
  if instruction = .op .SGT then
    if s.stack.length < 1024 then
      match s.stack with
      | a :: b :: rest => some {s with stack := UInt256.sgt a b :: rest, pc := s.pc.succ}
      | _ => none
    else none
  else runInstr instruction s

def runLocatedS {artifact : ProgramArtifact} {fork : Fork}
    (located : Located artifact fork) (s : State) : Option State :=
  if s.pc.toNat = artifact.instructionPC located.index then
    runInstrS located.instruction s
  else none

def runLocatedBlockS {artifact : ProgramArtifact} {fork : Fork} :
    List (Located artifact fork) → State → Option State
  | [], s => some s
  | located :: rest, s =>
      match runLocatedS located s with
      | none => none
      | some next =>
          match rest with
          | [] => some next
          | _ :: _ =>
              match next.halt with
              | .Running => runLocatedBlockS rest next
              | _ => none

theorem runInstrS_executionEnv {instruction : Instr} {s t : State}
    (h : runInstrS instruction s = some t) : t.executionEnv = s.executionEnv := by
  unfold runInstrS at h
  split at h
  · split at h
    · cases hs : s.stack with
      | nil => simp [hs] at h
      | cons a tail =>
          cases ht : tail with
          | nil => simp [hs, ht] at h
          | cons b rest =>
              simp only [hs, ht, Option.some.injEq] at h
              subst t
              rfl
    · simp at h
  · exact runInstr_executionEnv h

theorem runLocatedS_executionEnv {artifact : ProgramArtifact} {fork : Fork}
    {located : Located artifact fork} {s t : State}
    (h : runLocatedS located s = some t) : t.executionEnv = s.executionEnv := by
  unfold runLocatedS at h
  split at h
  · exact runInstrS_executionEnv h
  · simp at h

def runLocatedS_sound {artifact : ProgramArtifact} {fork : Fork}
    {located : Located artifact fork} {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedS located s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t := by
  unfold runLocatedS at hresult
  split at hresult
  · rename_i hpc
    by_cases hsgt : located.instruction = .op .SGT
    · have hwf : WellFormed s.fork located.instruction := by
        simpa [hfork] using located.wellFormed
      have hdec := decodes_of_artifact artifact s located.index located.instruction
        hcode hpc located.atIndex hwf
      rw [hsgt] at hdec
      change s.decodedOp = some .SGT at hdec
      unfold runInstrS at hresult
      rw [if_pos hsgt] at hresult
      split at hresult
      · rename_i hcap
        cases hs : s.stack with
        | nil => simp [hs] at hresult
        | cons a tail =>
            cases ht : tail with
            | nil => simp [hs, ht] at hresult
            | cons b rest =>
                simp only [hs, ht, Option.some.injEq] at hresult
                subst t
                apply TnM128SgtStep.gasStep_sgt hdec (by simp [hs, ht]) _ hrun hnp
                simp only [Operation.pushArity, Operation.popArity]
                omega
      · simp at hresult
    · have hloc : runLocated located s = some t := by
        simpa only [runLocated, if_pos hpc, runInstrS, if_neg hsgt] using hresult
      exact runLocated_sound hcode hfork hloc hrun hnp
  · simp at hresult

def runLocatedBlockS_sound (artifact : ProgramArtifact) (fork : Fork)
    (path : List (Located artifact fork)) {s t : State}
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hresult : runLocatedBlockS path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t := by
  induction path generalizing s t with
  | nil =>
      simp [runLocatedBlockS] at hresult
      subst t
      exact GasSteps.refl s
  | cons located rest ih =>
      cases rest with
      | nil =>
          cases hnext : runLocatedS located s with
          | none => simp [runLocatedBlockS, hnext] at hresult
          | some next =>
              simp [runLocatedBlockS, hnext] at hresult
              subst t
              exact runLocatedS_sound hcode hfork hnext hrun hnp
      | cons nextLocated tail =>
          cases hnext : runLocatedS located s with
          | none => simp [runLocatedBlockS, hnext] at hresult
          | some next =>
              cases hnextRun : next.halt with
              | Running =>
                  simp [runLocatedBlockS, hnext, hnextRun] at hresult
                  have henv := runLocatedS_executionEnv hnext
                  have hnextCode : next.executionEnv.code = artifact.code := by rw [henv, hcode]
                  have hnextFork : next.fork = fork := by
                    change next.executionEnv.fork = fork
                    rw [henv]
                    exact hfork
                  have hnextNp : Precompile.isPrecompileWithConfig next.executionEnv.precompileConfig
                      next.executionEnv.fork next.executionEnv.codeAddr = false := by
                    rw [henv]
                    exact hnp
                  exact (runLocatedS_sound hcode hfork hnext hrun hnp).trans
                    (ih hnextCode hnextFork hresult hnextRun hnextNp)
              | Success => simp [runLocatedBlockS, hnext, hnextRun] at hresult
              | Returned => simp [runLocatedBlockS, hnext, hnextRun] at hresult
              | Reverted => simp [runLocatedBlockS, hnext, hnextRun] at hresult
              | Exception error => simp [runLocatedBlockS, hnext, hnextRun] at hresult
end CycleSubmission.Global.Fast.SignedTopBit
