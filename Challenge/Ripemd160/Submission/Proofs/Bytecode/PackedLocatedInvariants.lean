import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRunOpBridge

set_option warningAsError true
set_option autoImplicit false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedInvariants

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PackedRunOpBridge PackedStep0

/-- Successful located blocks preserve the execution environment. This is
independent of the packed arithmetic and does not assert memory or PC equality. -/
theorem block_executionEnv {artifact : ProgramArtifact} {fork : Fork}
    {path : List (Stepper.Located artifact fork)} {s t : State}
    (hresult : Stepper.runLocatedBlock path s = some t) :
    t.executionEnv = s.executionEnv := by
  induction path generalizing s with
  | nil =>
      simp only [Stepper.runLocatedBlock, Option.some.injEq] at hresult
      subst t
      rfl
  | cons located rest ih =>
      cases hnext : Stepper.runLocated located s with
      | none => simp [Stepper.runLocatedBlock, hnext] at hresult
      | some next =>
          have henv := Stepper.runLocated_executionEnv hnext
          cases rest with
          | nil =>
              simp only [Stepper.runLocatedBlock, hnext, Option.some.injEq] at hresult
              subst t
              exact henv
          | cons following tail =>
              have htail : Stepper.runLocatedBlock (following :: tail) next = some t := by
                cases hhalt : next.halt <;>
                  simp_all [Stepper.runLocatedBlock]
              exact (ih htail).trans henv

#print axioms block_executionEnv

/-- A packed located plan contains no halting instruction. Successful
execution therefore retains the incoming running status through the last site. -/
theorem block_running {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)} {s t : State}
    (plan : LocatedPlan ops path s) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hresult : Stepper.runLocatedBlock path s = some t) :
    t.halt = .Running := by
  induction ops generalizing path s with
  | nil =>
      cases path with
      | nil =>
          simp only [Stepper.runLocatedBlock, Option.some.injEq] at hresult
          subst t
          exact hrun
      | cons located tail => simp [LocatedPlan] at plan
  | cons op ops ih =>
      cases path with
      | nil => simp [LocatedPlan] at plan
      | cons located tail =>
          rcases plan with ⟨shape, hcap, hpc, htail⟩
          let encoding : EncodesOp s.fork op located.instruction :=
            ⟨shape, by simpa [hfork] using located.wellFormed⟩
          cases hstep : Stepper.runInstr located.instruction s with
          | none =>
              simp [Stepper.runLocatedBlock, Stepper.runLocated, hpc, hstep] at hresult
          | some next =>
              have hnextRun : next.halt = .Running :=
                (runInstr_halt_of_encoding encoding hcap hstep).trans hrun
              have hnextFork : next.fork = fork := by
                change next.executionEnv.fork = fork
                rw [Stepper.runInstr_executionEnv hstep]
                exact hfork
              cases tail with
              | nil =>
                  simp only [Stepper.runLocatedBlock, Stepper.runLocated,
                    if_pos hpc, hstep, Option.some.injEq] at hresult
                  subst t
                  exact hnextRun
              | cons following rest =>
                  have hrest : Stepper.runLocatedBlock (following :: rest) next = some t := by
                    simpa only [Stepper.runLocatedBlock, Stepper.runLocated,
                      if_pos hpc, hstep, hnextRun] using hresult
                  exact ih (htail next hstep) hnextFork hnextRun hrest

#print axioms block_running

theorem instruction_callStack {s next : State} {op : Op}
    {instruction : YulEvmCompiler.Instr}
    (encoding : EncodesOp s.fork op instruction)
    (hcap : s.stack.length < 1024)
    (hstep : Stepper.runInstr instruction s = some next) :
    next.callStack = s.callStack := by
  cases encoding.shape <;>
    unfold Stepper.runInstr at hstep <;>
    rw [if_pos hcap] at hstep
  all_goals
    repeat' first | split at hstep | simp_all
  all_goals (subst next; rfl)

theorem block_callStack {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)} {s t : State}
    (plan : LocatedPlan ops path s) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hresult : Stepper.runLocatedBlock path s = some t) :
    t.callStack = s.callStack := by
  induction ops generalizing path s with
  | nil =>
      cases path with
      | nil =>
          simp only [Stepper.runLocatedBlock, Option.some.injEq] at hresult
          subst t
          rfl
      | cons located tail => simp [LocatedPlan] at plan
  | cons op ops ih =>
      cases path with
      | nil => simp [LocatedPlan] at plan
      | cons located tail =>
          rcases plan with ⟨shape, hcap, hpc, htail⟩
          let encoding : EncodesOp s.fork op located.instruction :=
            ⟨shape, by simpa [hfork] using located.wellFormed⟩
          cases hstep : Stepper.runInstr located.instruction s with
          | none =>
              simp [Stepper.runLocatedBlock, Stepper.runLocated, hpc, hstep] at hresult
          | some next =>
              have hnextRun : next.halt = .Running :=
                (runInstr_halt_of_encoding encoding hcap hstep).trans hrun
              have hcalls := instruction_callStack encoding hcap hstep
              have hnextFork : next.fork = fork := by
                change next.executionEnv.fork = fork
                rw [Stepper.runInstr_executionEnv hstep]
                exact hfork
              cases tail with
              | nil =>
                  simp only [Stepper.runLocatedBlock, Stepper.runLocated,
                    if_pos hpc, hstep, Option.some.injEq] at hresult
                  subst t
                  exact hcalls
              | cons following rest =>
                  have hrest : Stepper.runLocatedBlock (following :: rest) next = some t := by
                    simpa only [Stepper.runLocatedBlock, Stepper.runLocated,
                      if_pos hpc, hstep, hnextRun] using hresult
                  exact (ih (htail next hstep) hnextFork hnextRun hrest).trans hcalls

#print axioms block_callStack

/-- Package all preserved outer-state fields with the existing local-cap gas
certificate. Endpoint PC remains a separate exact-site obligation. -/
theorem certificate_preserved {artifact : ProgramArtifact} {fork : Fork}
    {ops : List Op} {path : List (Stepper.Located artifact fork)}
    {s : State} {out : List UInt256}
    (sequence : StraightLineLocated ops path)
    (hbudget : s.stack.length + ops.length < 1024)
    (hstart : PathStarts path s)
    (hcode : s.executionEnv.code = artifact.code)
    (hfork : s.fork = fork) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (habstract : runOps (memoryWord s) ops s.stack = some out) :
    ∃ t, Stepper.runLocatedBlock path s = some t ∧
      ∃ _trace : GasSteps s t,
        t.stack = out ∧ t.memory = s.memory ∧
        t.executionEnv = s.executionEnv ∧ t.halt = .Running ∧
        t.callStack = s.callStack := by
  obtain ⟨t, hblock, trace, hstack, hmemory⟩ :=
    roundsCertificate sequence hbudget hstart hcode hfork hrun hnp habstract
  have plan := locatedPlan_of_straightLine sequence hbudget hstart hfork
  exact ⟨t, hblock, trace, hstack, hmemory, block_executionEnv hblock,
    block_running plan hfork hrun hblock, block_callStack plan hfork hrun hblock⟩

#print axioms certificate_preserved

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedInvariants
