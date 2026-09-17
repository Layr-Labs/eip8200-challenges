import Challenge.Modexp.Submission.LocalPatch.TransportArithmetic
import Challenge.Modexp.Submission.LocalPatch.TransportBitwise
import Challenge.Modexp.Submission.LocalPatch.TransportStack
import Challenge.Modexp.Submission.LocalPatch.TransportMemory
import Challenge.Modexp.Submission.LocalPatch.TransportControl

set_option warningAsError true

/-!
This is the actual Step transport theorem. No equivalence-of-step field is
assumed. The source's successful suffix is used only to exclude exceptional
source transitions: forcing a cheaper candidate to reproduce source OOG would
be an incorrect requirement for the protected sufficiently-large-gas predicate.
-/
namespace Challenge.Modexp.Submission.LocalPatch.Transport

open EvmSemantics EvmSemantics.EVM

/-- The precompile gate used in Step.running. It observes neither code array. -/
def NonPrecompile (s : State) : Prop :=
  Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
    s.executionEnv.fork s.executionEnv.codeAddr = false

theorem initial_nonPrecompile (code input : ByteArray) (gas : Nat) :
    NonPrecompile (initialState code input gas) := by
  change Precompile.isPrecompileWithConfig executionConfig .Osaka deployAddress = false
  decide

/-- A top-level non-precompile Step is necessarily a StepRunning derivation. -/
theorem running_of_step {s t : State} (hcall : s.callStack = [])
    (hnp : NonPrecompile s) (hstep : Step s t) :
    s.halt = .Running ∧ StepRunning s t := by
  cases hstep with
  | running hr _ hs => exact ⟨hr, hs⟩
  | precompileSuccess _output _gasUsed _hr hp _hprec =>
      have hbad : false = true := hnp.symm.trans hp
      cases hbad
  | precompileOog _hr hp _hprec =>
      have hbad : false = true := hnp.symm.trans hp
      cases hbad
  | returning hs =>
      cases hs <;> simp_all

/-- Dispatch to the closed opcode-family inversion proofs. -/
theorem ordinary_running {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hlayout : JumpDestLayout.check s.executionEnv.code code = true)
    (hallowed : Has ordinary s) (hnormal : NoException t)
    (hstep : StepRunning s t) :
    StepRunning (liftState code credit counter s) (liftState code credit counter t) := by
  rcases ordinary_cases hallowed with h | h | h | h | h
  · exact arithmetic_running hwindow h hnormal hstep
  · exact bitwise_running hwindow h hnormal hstep
  · exact stack_running hwindow h hnormal hstep
  · exact memoryInput_running hwindow h hnormal hstep
  · exact control_running hwindow hlayout h hnormal hstep

/-- Main result: same local decode, all-target JUMPDEST preservation, supported
opcode, single-frame non-native execution, and a successful source suffix imply
one actual candidate Step. The target may carry an arbitrary nonnegative gas
surplus and an unrelated execLength. There is no precondition equating code. -/
theorem ordinary_step {code : ByteArray} {credit counter : Nat} {s t : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true)
    (hlayout : JumpDestLayout.check s.executionEnv.code code = true)
    (hallowed : Has ordinary s) (hcall : s.callStack = [])
    (hnp : NonPrecompile s) (hstep : Step s t)
    (hsuffix : ∃ output : ByteArray, Eval t (.returned output)) :
    Step (liftState code credit counter s) (liftState code credit counter t) := by
  obtain ⟨hrun, hs⟩ := running_of_step hcall hnp hstep
  obtain ⟨_, _, _, hc, _⟩ := ordinary_context hs hallowed
  have hn := noException_of_successful (hc.trans hcall) hsuffix
  exact Step.running hrun hnp (ordinary_running hwindow hlayout hallowed hn hs)

/-- The code-specific world and precompile gate are preserved at source steps;
this proves those invariant clauses, leaving only the finite opcode/PC-domain
and macro-entry clauses to the independent reachability work. -/
theorem ordinary_source_invariant {reference : ByteArray} {s t : State}
    (hworld : FixedWorld reference s) (hnp : NonPrecompile s)
    (hallowed : Has ordinary s) (hstep : Step s t) :
    FixedWorld reference t ∧ NonPrecompile t := by
  obtain ⟨_, hs⟩ := running_of_step hworld.2.2.2 hnp hstep
  have hworld' := fixedWorld_next hworld hs hallowed
  have he := (ordinary_context hs hallowed).1
  refine ⟨hworld', ?_⟩
  unfold NonPrecompile
  rw [he]
  exact hnp

/-- The ordinary arm of ForwardRefinement.step, now discharged by actual Step
constructors. A patch dispatcher must invoke it only at verified unchanged
windows; invoking it inside a differing macro cannot satisfy hwindow. -/
theorem related_ordinary_step {reference candidate : ByteArray} {s next target : State}
    (hrel : Related reference candidate s target)
    (hwindow : LocalDecode.checkAt reference candidate s.pc.toNat = true)
    (hlayout : JumpDestLayout.check reference candidate = true)
    (hallowed : Has ordinary s) (hnp : NonPrecompile s)
    (hstep : Step s next)
    (hsuffix : ∃ output : ByteArray, Eval next (.returned output)) :
    ∃ targetNext : State, Steps target targetNext ∧
      Related reference candidate next targetNext := by
  obtain ⟨hworld, credit, counter, rfl⟩ := hrel
  have hw : LocalDecode.checkAt s.executionEnv.code candidate s.pc.toNat = true := by
    rw [hworld.1]
    exact hwindow
  have hl : JumpDestLayout.check s.executionEnv.code candidate = true := by
    rw [hworld.1]
    exact hlayout
  have hs := ordinary_step (credit := credit) (counter := counter)
    hw hl hallowed hworld.2.2.2 hnp hstep hsuffix
  have hn := (ordinary_source_invariant hworld hnp hallowed hstep).1
  exact ⟨liftState candidate credit counter next, Steps.trans hs (Steps.refl _),
    hn, credit, counter, rfl⟩

/-- Finite unchanged-PC certificate adapter. No opcode reachability assertion is
inferred merely because a finite list was checked. Membership is explicit. -/
theorem related_ordinary_step_of_checkMany
    {reference candidate : ByteArray} {pcs : List Nat} {s next target : State}
    (hrel : Related reference candidate s target)
    (hwindows : LocalDecode.checkMany reference candidate pcs = true)
    (hpc : s.pc.toNat ∈ pcs)
    (hlayout : JumpDestLayout.check reference candidate = true)
    (hallowed : Has ordinary s) (hnp : NonPrecompile s)
    (hstep : Step s next)
    (hsuffix : ∃ output : ByteArray, Eval next (.returned output)) :
    ∃ targetNext : State, Steps target targetNext ∧
      Related reference candidate next targetNext := by
  have hat : LocalDecode.checkAt reference candidate s.pc.toNat = true :=
    (List.all_eq_true.mp hwindows) s.pc.toNat hpc
  exact related_ordinary_step hrel hat hlayout hallowed hnp hstep hsuffix

end Challenge.Modexp.Submission.LocalPatch.Transport
