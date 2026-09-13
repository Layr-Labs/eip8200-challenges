import Challenge.Ripemd160.Submission.Proofs.Bytecode.DataStepper

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.EvmProof.RawLocatedSequence
open EvmSemantics EvmSemantics.EVM YulEvmCompiler DataStepper

/-- A raw byte offset with its exact decoder certificate, independent of any
executable-prefix instruction index. -/
structure Located (code : ByteArray) (fork : Fork) where
  pc : Nat
  instruction : Instr
  decodes : ∀ s : State, s.executionEnv.code = code → s.fork = fork →
    s.pc.toNat = pc → Decodes s instruction

def runLocated {code fork} (l : Located code fork) (s : State) : Option State :=
  if s.pc.toNat = l.pc then runInstr l.instruction s else none

def runBlock {code fork} : List (Located code fork) → State → Option State
  | [], s => some s
  | l :: rest, s =>
    match runLocated l s with
    | none => none
    | some next =>
      match rest with
      | [] => some next
      | _ :: _ =>
        match next.halt with
        | .Running => runBlock rest next
        | _ => none

def runLocated_sound {code fork} {l : Located code fork} {s t : State}
    (hcode : s.executionEnv.code = code) (hfork : s.fork = fork)
    (hresult : runLocated l s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t := by
  unfold runLocated at hresult
  split at hresult
  next hpc => exact runInstr_sound (l.decodes s hcode hfork hpc) hresult hrun hnp
  next => simp_all

theorem runLocated_executionEnv {code fork} {l : Located code fork} {s t : State}
    (h : runLocated l s = some t) : t.executionEnv = s.executionEnv := by
  unfold runLocated at h
  split at h
  next => exact runInstr_executionEnv h
  next => simp_all

def runBlock_sound {code fork} (path : List (Located code fork)) {s t : State}
    (hcode : s.executionEnv.code = code) (hfork : s.fork = fork)
    (hresult : runBlock path s = some t) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) : GasSteps s t := by
  induction path generalizing s t with
  | nil =>
    simp [runBlock] at hresult
    subst t
    exact GasSteps.refl s
  | cons l rest ih =>
    cases hnext : runLocated l s with
    | none => simp [runBlock, hnext] at hresult
    | some next =>
      cases rest with
      | nil =>
        simp [runBlock, hnext] at hresult
        subst t
        exact runLocated_sound hcode hfork hnext hrun hnp
      | cons l2 tail =>
        cases hhalt : next.halt with
        | Running =>
          have hrest : runBlock (l2 :: tail) next = some t := by
            simpa [runBlock, hnext, hhalt] using hresult
          have he := runLocated_executionEnv hnext
          have hc : next.executionEnv.code = code := by rw [he, hcode]
          have hf : next.fork = fork := by
            change next.executionEnv.fork = fork
            rw [he]
            exact hfork
          have hn : Precompile.isPrecompileWithConfig next.executionEnv.precompileConfig
              next.executionEnv.fork next.executionEnv.codeAddr = false := by
            rw [he]
            exact hnp
          exact (runLocated_sound hcode hfork hnext hrun hnp).trans
            (ih hc hf hrest hhalt hn)
        | Success => simp [runBlock, hnext, hhalt] at hresult
        | Returned => simp [runBlock, hnext, hhalt] at hresult
        | Reverted => simp [runBlock, hnext, hhalt] at hresult
        | Exception err => simp [runBlock, hnext, hhalt] at hresult

#print axioms runBlock_sound
end Challenge.EvmProof.RawLocatedSequence
