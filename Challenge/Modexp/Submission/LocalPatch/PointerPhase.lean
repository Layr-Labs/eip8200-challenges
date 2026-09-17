import Challenge.Modexp.Submission.LocalPatch.PointerContext
import Challenge.Modexp.Submission.LocalPatch.PointerPrefix
import Challenge.Modexp.Submission.LocalPatch.PointerCandidateRun

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Transport
open Challenge.Modexp.Submission.Isolation

/-- Candidate-local *byte/layout* evidence. There is no Step/Eval/Correct
assumption. The concrete frontier64 companion discharges all three fields. -/
structure Sites (candidate : ByteArray) : Prop where
  code : NewCode candidate
  windows : LocalDecode.checkMany reference candidate
    (StaticDomainFrontier64.pcs.filter fun pc => decide (Exterior pc)) = true
  targets : ∀ n, Decode.isValidJumpDest reference n = Decode.isValidJumpDest candidate n

/-- Synchronized outside states, or one of the four proper old prefixes with
the candidate paused at the original entry. A proper prefix has only the
budget/capacity forced by the actual source instructions already observed. -/
inductive Phase (candidate : ByteArray) : State → State → Prop
  | sync {s t : State} (ctx : Context s)
      (outside : s.halt = .Running → ¬ Interior s.pc.toNat)
      (same : Related reference candidate s t) : Phase candidate s t
  | paused (a : State) (p : UInt256) (tail : List UInt256)
      (j credit counter : Nat)
      (current : Context (pre a p tail j)) (anchor : Context a)
      (run : a.halt = .Running) (pc : a.pc = UInt256.ofNat 2539)
      (stack : a.stack = p :: tail) (positive : 1 ≤ j) (proper : j < 5)
      (budget : 3 * j ≤ a.gasAvailable) (capacity : Capacity j tail) :
      Phase candidate (pre a p tail j) (liftState candidate credit counter a)

/-- The whole successful-step dispatcher, with both actual source-prefix
inversion and target execution implemented. -/
theorem phase_step {candidate : ByteArray} (sites : Sites candidate)
    {source next target : State} (hp : Phase candidate source target)
    (hs : Step source next)
    (hsuffix : ∃ output : ByteArray, Eval next (.returned output)) :
    ∃ targetNext, Steps target targetNext ∧ Phase candidate next targetNext := by
  cases hp with
  | sync ctx outside same =>
    obtain ⟨hr, hrun⟩ := running_of_step ctx.world.2.2.2 ctx.nonprecompile hs
    have cn := ctx.next hs
    by_cases he : source.pc.toNat = 2539
    · have hew : source.pc = UInt256.ofNat 2539 := Word.word_ext he
      have hn := noException_of_successful cn.world.2.2.2 hsuffix
      obtain ⟨p, tail, hstack, hbudget, hcap, hnxt⟩ :=
        start_inverse oldCode ctx.world.1 ctx.fork hew hn hrun
      obtain ⟨_, credit, counter, rfl⟩ := same
      subst next
      exact ⟨liftState candidate credit counter source, Steps.refl _,
        Phase.paused source p tail 1 credit counter cn ctx hr hew hstack
          (by decide) (by decide) hbudget hcap⟩
    · have hout := outside hr
      have hext : Exterior source.pc.toNat := by
        dsimp [Interior, Exterior, entryPC, exitPC] at hout ⊢
        omega
      have hmem : source.pc.toNat ∈
          StaticDomainFrontier64.pcs.filter (fun pc => decide (Exterior pc)) := by
        exact List.mem_filter.mpr ⟨(ctx.facts hr).1, decide_eq_true hext⟩
      have hwindow : LocalDecode.checkAt reference candidate source.pc.toNat = true :=
        (List.all_eq_true.mp sites.windows) _ hmem
      obtain ⟨hw, credit, counter, rfl⟩ := same
      have hs' := ordinary_step_targets (credit := credit) (counter := counter)
        (by simpa only [hw.1] using hwindow)
        (by simpa only [hw.1] using sites.targets)
        (ctx.facts hr).2 hw.2.2.2 ctx.nonprecompile hs hsuffix
      exact ⟨liftState candidate credit counter next,
        Steps.trans hs' (Steps.refl _),
        Phase.sync cn (ctx.next_outside hext hs) ⟨cn.world, credit, counter, rfl⟩⟩
  | paused a p tail j credit counter current anchor run pc stack positive proper budget capacity =>
    have cn := current.next hs
    obtain ⟨_, hrun⟩ := running_of_step current.world.2.2.2 current.nonprecompile hs
    have hn := noException_of_successful cn.world.2.2.2 hsuffix
    obtain ⟨hb, hc, ht⟩ := next_inverse oldCode a p tail j positive proper
      anchor.world.1 anchor.fork budget capacity hn hrun
    subst next
    by_cases hlast : j + 1 = 5
    · have hj : j = 4 := by omega
      subst j
      have hc' : tail.length + 2 < 1024 := by simpa [Capacity] using hc
      let tr := candidateTrace sites.code a p tail counter pc stack run anchor.fork
        anchor.nonprecompile hc'
      have htgt := discounted_macro candidate 15 credit counter counter
        hb (show (pre a p tail 5).gasAvailable = a.gasAvailable - 15 from rfl)
        tr (show tr.cost ≤ 15 from by change 12 ≤ 15; decide)
      exact ⟨liftState candidate (credit + (15 - tr.cost)) counter (pre a p tail 5),
        htgt, Phase.sync cn (by intro _; change ¬ (2539 < 2545 ∧ 2545 < 2545); omega)
          ⟨cn.world, credit + (15 - tr.cost), counter, rfl⟩⟩
    · have hproper : j + 1 < 5 := by omega
      exact ⟨liftState candidate credit counter a, Steps.refl _,
        Phase.paused a p tail (j + 1) credit counter cn anchor run pc stack
          (by omega) hproper hb hc⟩

theorem phase_finish {candidate : ByteArray} {source target : State}
    {output : ByteArray} (hp : Phase candidate source target)
    (hh : source.halt ≠ .Running) (hc : source.callStack = [])
    (hr : source.toResult = .returned output) :
    ∃ final, Steps target final ∧ final.halt ≠ .Running ∧
      final.callStack = [] ∧ final.toResult = .returned output := by
  cases hp with
  | sync ctx outside same => exact related_finish same hh hc hr
  | paused a p tail j credit counter current anchor run pc stack positive proper budget capacity =>
    exact (hh ((pre_halt a p tail j).trans run)).elim

/-- Complete nonidentity refinement constructor. Only finite code/layout
certificates remain as arguments, and the frontier64 companion supplies them. -/
def refinement {candidate : ByteArray} (sites : Sites candidate) :
    ForwardRefinement reference candidate where
  referenceGas := fun gas => gas
  cofinal := fun bound => ⟨bound, fun _ h => h⟩
  Related := Phase candidate
  entry := by
    intro input _ gas
    exact Phase.sync (Context.initial input gas)
      (by intro _; change ¬ (2539 < 0 ∧ 0 < 2545); omega)
      (related_entry reference candidate input gas)
  step := phase_step sites
  finish := phase_finish

end Challenge.Modexp.Submission.LocalPatch.PointerSub32
