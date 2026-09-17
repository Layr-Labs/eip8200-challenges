import Challenge.Modexp.Submission.LocalPatch.PointerReferenceFacts
import Challenge.Modexp.Submission.LocalPatch.StaticExecutionFrontier64
import Challenge.Modexp.Submission.LocalPatch.OrdinaryTargets

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.PointerSub32
open EvmSemantics EvmSemantics.EVM
open Transport StaticDomain

/-- Actual source-prefix evidence; no candidate equivalence occurs here. -/
structure Context (s : State) : Prop where
  world : FixedWorld reference s
  nonprecompile : NonPrecompile s
  fork : s.fork = .Osaka
  execution : ∃ input gas, Steps (initialState reference input gas) s

theorem safe_ordinary (op : Operation) (hs : transportSafe op = true) :
    ordinary op = true := by
  cases op with
  | StopArith a => cases a <;> rfl
  | CompBit a => rfl
  | Keccak a => simp [transportSafe] at hs
  | Env a => cases a <;> simp_all [transportSafe, ordinary, arithmetic,
      bitwise, stackOps, memoryInput, control]
  | Block a => simp [transportSafe] at hs
  | StackMemFlow a => cases a <;> simp_all [transportSafe, ordinary, arithmetic,
      bitwise, stackOps, memoryInput, control]
  | Push a => rfl
  | Dup a => rfl
  | Swap a => rfl
  | DupN a => simp [transportSafe] at hs
  | SwapN a => simp [transportSafe] at hs
  | Exchange a => simp [transportSafe] at hs
  | Log a => simp [transportSafe] at hs
  | System a => cases a <;> simp_all [transportSafe, ordinary, arithmetic,
      bitwise, stackOps, memoryInput, control]

namespace Context

def initial (input : ByteArray) (gas : Nat) : Context (initialState reference input gas) where
  world := ⟨rfl, rfl, rfl, rfl⟩
  nonprecompile := initial_nonPrecompile _ _ _
  fork := rfl
  execution := ⟨input, gas, Steps.refl _⟩

theorem facts {s : State} (ctx : Context s) (hr : s.halt = .Running) :
    s.pc.toNat ∈ StaticDomainFrontier64.pcs ∧ Has ordinary s := by
  obtain ⟨input, gas, hp⟩ := ctx.execution
  obtain ⟨_, _, _, _, hm, op, imm, hd, hs⟩ :=
    StaticExecutionFrontier64.running_endpoint input gas hp hr
  have hop : s.decodedOp = some op := congrArg (fun d => d.map Prod.fst) hd
  exact ⟨hm, by simpa only [Has, hop] using safe_ordinary op hs⟩

/-- Reuses the separately owned actual-Step domain theorem and the closed
ordinary context inversion; the baseline Correct theorem is not inspected. -/
theorem next {s t : State} (ctx : Context s) (hs : Step s t) : Context t := by
  obtain ⟨hr, hrun⟩ := running_of_step ctx.world.2.2.2 ctx.nonprecompile hs
  have ha := (ctx.facts hr).2
  obtain ⟨hw, hn⟩ := ordinary_source_invariant ctx.world ctx.nonprecompile ha hs
  have he := (ordinary_context hrun ha).1
  obtain ⟨input, gas, hp⟩ := ctx.execution
  exact ⟨hw, hn, by change t.executionEnv.fork = .Osaka; rw [he]; exact ctx.fork,
    input, gas, hp.snoc hs⟩

/-- The only incoming edge permitted by the phase dispatcher is the macro
entry. Every proper interior excludes all actual dynamic jump destinations. -/
theorem next_outside {s t : State} (ctx : Context s)
    (he : Exterior s.pc.toNat) (hs : Step s t) :
    t.halt = .Running → ¬ Interior t.pc.toNat := by
  intro ht
  obtain ⟨hr, _⟩ := running_of_step ctx.world.2.2.2 ctx.nonprecompile hs
  obtain ⟨input, gas, hp⟩ := ctx.execution
  have hout := StaticExecutionFrontier64.step_from_running_endpoint input gas hp hr hs
  rcases hout with terminal | ⟨_, _, _, hsucc⟩
  · exact (terminal.1 ht).elim
  · exact exterior_no_entry (ctx.facts hr).1 he hsucc

end Context
end Challenge.Modexp.Submission.LocalPatch.PointerSub32
