import Challenge.Modexp.Spec
import Challenge.EvmProof.Gas

set_option warningAsError true

/-!
A code-independent, successful-execution refinement rule for MODEXP.

This module imports neither any Submission byte provider nor Benchmark.Artifact.
The source evaluation is the pinned EVM relation, with real gas, account maps,
call stack, memory, PCs and halt state. The candidate may take zero, one or many
steps for one source step. Its terminal obligation must complete an actual
finite execution; stuttering does not assume termination.

Only successful source suffixes need simulation. Requiring the same exceptional
outcome at insufficient gas would reject otherwise valid gas improvements and
would be stronger than Challenge.Modexp.Correct.
-/

namespace Challenge.Modexp.Submission.Isolation

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

/-- A state relation sufficient to transport successful evaluations.

`referenceGas` is cofinal, not necessarily the identity. Thus this interface
preserves the original sufficiently-large-gas generality; it does not require
equal instruction counts, equal gas costs, or a fixed execution-fuel bound.

For a concrete patch, `Related` must account for both initial account maps as
well as the active environment's code. It may include internal patch phases.
There is deliberately no purported automatic code-rebinding lemma here. -/
structure ForwardRefinement (reference candidate : ByteArray) where
  referenceGas : Nat → Nat
  cofinal : ∀ bound : Nat, ∃ threshold : Nat,
    ∀ gas : Nat, threshold ≤ gas → bound ≤ referenceGas gas
  Related : State → State → Prop
  entry : ∀ input : ByteArray, ValidInput input → ∀ gas : Nat,
    Related (initialState reference input (referenceGas gas))
      (initialState candidate input gas)
  step : ∀ {source next target : State},
    Related source target → Step source next →
    (∃ output : ByteArray, Eval next (.returned output)) →
    ∃ targetNext : State, Steps target targetNext ∧ Related next targetNext
  finish : ∀ {source target : State} {output : ByteArray},
    Related source target → source.halt ≠ .Running → source.callStack = [] →
    source.toResult = .returned output →
    ∃ final : State, Steps target final ∧ final.halt ≠ .Running ∧
      final.callStack = [] ∧ final.toResult = .returned output

namespace ForwardRefinement

/-- Reuse a source evaluation, not the implementation of its correctness proof. -/
theorem transferEval {reference candidate : ByteArray}
    (f : ForwardRefinement reference candidate)
    {source target : State} {output : ByteArray}
    (h : Eval source (.returned output)) (hrel : f.Related source target) :
    Eval target (.returned output) := by
  have aux : ∀ {s : State} {r : ExecutionResult}, Eval s r →
      ∀ {t : State}, f.Related s t → ∀ out : ByteArray,
        r = .returned out → Eval t (.returned out) := by
    intro s r hs
    induction hs with
    | halted hhalt hstack =>
      intro t hst out hr
      obtain ⟨final, trace, halted, stack, result⟩ :=
        f.finish hst hhalt hstack hr
      exact Eval.iff_steps_halted.mpr ⟨final, trace, halted, stack, result⟩
    | stepThen hstep htail ih =>
      intro t hst out hr
      have successful : ∃ out' : ByteArray, Eval _ (.returned out') :=
        ⟨out, by simpa only [hr] using htail⟩
      obtain ⟨next, tracePrefix, hnext⟩ := f.step hst hstep successful
      have suffix := ih hnext out hr
      obtain ⟨final, trace, halted, stack, result⟩ := Eval.iff_steps_halted.mp suffix
      exact Eval.iff_steps_halted.mpr
        ⟨final, tracePrefix.append trace, halted, stack, result⟩
  exact aux h hrel output rfl

/-- End-to-end bridge to the unmodified protected acceptance predicate. -/
theorem correct {reference candidate : ByteArray}
    (f : ForwardRefinement reference candidate) (href : Correct reference) :
    Correct candidate := by
  intro input hvalid
  obtain ⟨bound, hbound⟩ := href input hvalid
  obtain ⟨threshold, hthreshold⟩ := f.cofinal bound
  refine ⟨threshold, fun gas hgas => ?_⟩
  exact f.transferEval
    (hbound (f.referenceGas gas) (hthreshold gas hgas))
    (f.entry input hvalid gas)

/-- Closed control instance; it has no extra semantic premise. -/
def refl (code : ByteArray) : ForwardRefinement code code where
  referenceGas := fun gas => gas
  cofinal := fun bound => ⟨bound, fun _ h => h⟩
  Related := fun source target => source = target
  entry := fun _ _ _ => rfl
  step := by
    intro source next target hrel hstep _
    subst target
    exact ⟨next, Steps.trans hstep (Steps.refl next), rfl⟩
  finish := by
    intro source target output hrel hhalt hstack hresult
    subst target
    exact ⟨source, Steps.refl source, hhalt, hstack, hresult⟩

/-- Exact code equality is used only for the zero-byte-change control.
A nonidentical candidate must replace this instance with real execution proofs. -/
def ofEq {reference candidate : ByteArray} (h : candidate = reference) :
    ForwardRefinement reference candidate := by
  cases h
  exact refl _

end ForwardRefinement

/-- A gas-erased block contract is usable by the simulation only at a budget
that actually covers its cost. No statement equates arbitrary gas counters. -/
theorem realizeGasSteps {source target : State}
    (trace : GasSteps source target) (hgas : trace.cost ≤ source.gasAvailable) :
    Steps source (withGas target (source.gasAvailable - trace.cost)) := by
  have hself : withGas source source.gasAvailable = source := by
    cases source
    rfl
  have h := trace.trace source.gasAvailable hgas
  rw [hself] at h
  exact h

end Challenge.Modexp.Submission.Isolation
