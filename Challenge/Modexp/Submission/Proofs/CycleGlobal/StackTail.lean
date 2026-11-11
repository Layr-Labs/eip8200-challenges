import Challenge.EvmProof.Stepper
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-! Adapted from RIPEMD submission6f7231a3-1f75-46ac-bf4b-0545f8b52968,
source commit8b6490842b63f9009ea6058e26ea838389d72ed7. See dependencies.json. -/
namespace CycleSubmission.Global.StackTail
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def append (s : State) (rho : List UInt256) : State :=
  {s with stack := s.stack ++ rho}

private theorem get_append {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) (rho : List α) : (xs ++ rho)[i]? = some a := by
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
      cases i with
      | zero => simpa using h
      | succ i => exact ih h

private theorem get_bound {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.length := by
  by_contra hn
  have hz : xs[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
  rw [hz] at h
  contradiction

private theorem set_append {α : Type} (xs rho : List α) (i : Nat) (a : α)
    (hi : i < xs.length) : (xs ++ rho).set i a = xs.set i a ++ rho := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => rfl
      | succ i => simpa using ih i (by simpa using hi)

private theorem exchange_append {α : Type} {xs ys : List α} {i j : Nat}
    (h : xs.exchange i j = some ys) (rho : List α) :
    (xs ++ rho).exchange i j = some (ys ++ rho) := by
  unfold List.exchange at h ⊢
  cases ha : xs[i]? with
  | none => simp [ha] at h
  | some a =>
    cases hb : xs[j]? with
    | none => simp [ha, hb] at h
    | some b =>
      rw [ha, hb] at h
      change some ((xs.set i b).set j a) = some ys at h
      injection h with h
      subst ys
      rw [get_append ha rho, get_append hb rho]
      change some (((xs ++ rho).set i b).set j a) = some (((xs.set i b).set j a) ++ rho)
      rw [set_append xs rho i b (get_bound ha),
        set_append (xs.set i b) rho j a (by simpa using get_bound hb)]

private theorem exchange_length {α : Type} {xs ys : List α} {i j : Nat}
    (h : xs.exchange i j = some ys) : ys.length = xs.length := by
  unfold List.exchange at h
  cases ha : xs[i]? with
  | none => simp [ha] at h
  | some a =>
    cases hb : xs[j]? with
    | none => simp [ha, hb] at h
    | some b =>
      rw [ha, hb] at h
      change some ((xs.set i b).set j a) = some ys at h
      injection h with h
      subst ys
      simp

/-- A successful instruction only accesses its existing prefix. Extra lower words
are preserved when the combined stack has room. -/
theorem runInstr_append {instruction : Instr} {s t : State} (rho : List UInt256)
    (hcap : s.stack.length + rho.length < 1024)
    (hr : Stepper.runInstr instruction s = some t) :
    Stepper.runInstr instruction (append s rho) = some (append t rho) ∧
      t.stack.length ≤ s.stack.length + 1 := by
  have hs : s.stack.length < 1024 := by omega
  have hsr : (append s rho).stack.length < 1024 := by
    simpa only [append, List.length_append] using hcap
  cases instruction with
  | push width value =>
      simp only [Stepper.runInstr, if_pos hs] at hr
      split at hr <;> simp only [Option.some.injEq] at hr <;> subst t <;>
        simp_all [Stepper.runInstr, append]
  | op operation =>
    cases operation with
    | Dup n =>
      simp only [Stepper.runInstr, if_pos hs] at hr
      cases hg : s.stack[n.idx.val]? with
      | none => simp [hg] at hr
      | some value =>
        simp only [hg, Option.some.injEq] at hr
        subst t
        simp [Stepper.runInstr, append, hcap, get_append hg rho]
    | Swap n =>
      simp only [Stepper.runInstr, if_pos hs] at hr
      cases hg : s.stack.exchange 0 (n.idx.val + 1) with
      | none => simp [hg] at hr
      | some stack =>
        simp only [hg, Option.some.injEq] at hr
        subst t
        simp [Stepper.runInstr, append, hcap, exchange_append hg rho,
          exchange_length hg]
    | StopArith o | CompBit o | Env o | StackMemFlow o | System o =>
      cases o <;>
        rcases he : s.stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp only [Stepper.runInstr, if_pos hs, he] at hr <;>
        (try contradiction) <;>
        (repeat' first
          | split at hr
          | (simp only [Option.some.injEq] at hr; subst t; simp_all [Stepper.runInstr, append, State.activeWordsAfterUInt256, State.activeWordsAfterUInt256_2] <;> omega)
          | contradiction)
    | Keccak o | Block o => cases o <;> simp [Stepper.runInstr, hs] at hr
    | Push o | DupN o | SwapN o | Exchange o | Log o =>
      simp [Stepper.runInstr, hs] at hr

theorem runLocated_append {artifact : ProgramArtifact} {fork : Fork}
    {located : Stepper.Located artifact fork} {s t : State} (rho : List UInt256)
    (hcap : s.stack.length + rho.length < 1024)
    (hr : Stepper.runLocated located s = some t) :
    Stepper.runLocated located (append s rho) = some (append t rho) ∧
      t.stack.length ≤ s.stack.length + 1 := by
  unfold Stepper.runLocated at hr ⊢
  split at hr
  · rename_i hpc
    have hpc' : (append s rho).pc.toNat = artifact.instructionPC located.index := hpc
    rw [if_pos hpc']
    exact runInstr_append rho hcap hr
  · contradiction

theorem runLocatedBlock_append {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State} (rho : List UInt256)
    (hcap : s.stack.length + rho.length + path.length < 1024)
    (hr : Stepper.runLocatedBlock path s = some t) :
    Stepper.runLocatedBlock path (append s rho) = some (append t rho) ∧
      t.stack.length ≤ s.stack.length + path.length := by
  induction path generalizing s t with
  | nil =>
      simp only [Stepper.runLocatedBlock, Option.some.injEq] at hr
      subst t
      simp [Stepper.runLocatedBlock]
  | cons located rest ih =>
      cases hg : Stepper.runLocated located s with
      | none => simp [Stepper.runLocatedBlock, hg] at hr
      | some next =>
        have ha := runLocated_append rho (by simp only [List.length_cons] at hcap; omega) hg
        cases rest with
        | nil =>
          simp only [Stepper.runLocatedBlock, hg, Option.some.injEq] at hr
          subst t
          constructor
          · simp only [Stepper.runLocatedBlock, ha.1]
          · simpa using ha.2
        | cons nextLocated tail =>
          cases hh : next.halt with
          | Running =>
            have hn : Stepper.runLocatedBlock (nextLocated :: tail) next = some t := by
              simpa only [Stepper.runLocatedBlock, hg, hh] using hr
            have hi := ih (s := next) (by
              simp only [List.length_cons] at hcap ⊢
              have hlen := ha.2
              omega) hn
            constructor
            · have hh' : (append next rho).halt = .Running := hh
              simpa only [Stepper.runLocatedBlock, ha.1, hh'] using hi.1
            · simp only [List.length_cons] at *
              omega
          | Success | Returned | Reverted | Exception error =>
              simp [Stepper.runLocatedBlock, hg, hh] at hr

/-- Lift a certified finite path while preserving a bounded lower stack suffix. -/
def gasSteps {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State} (rho : List UInt256)
    (hcap : s.stack.length + rho.length + path.length < 1024)
    (hr : Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (append s rho) (append t rho) :=
  Stepper.runLocatedBlock_sound artifact fork path hcode hfork
    (runLocatedBlock_append path rho hcap hr).1 hrun hnp

#print axioms runInstr_append
#print axioms runLocatedBlock_append
#print axioms gasSteps
end CycleSubmission.Global.StackTail
