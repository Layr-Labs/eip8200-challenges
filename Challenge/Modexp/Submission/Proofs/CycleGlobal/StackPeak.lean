import Challenge.Modexp.Submission.Proofs.CycleGlobal.StackTail
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
noncomputable section
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.Global.StackPeak
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def pops : Instr → Nat
  | .push _ _ => 0
  | .op op => Operation.popArity op

def pushes : Instr → Nat
  | .push _ _ => 1
  | .op op => Operation.pushArity op

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

theorem runInstr_length {instruction : Instr} {s t : State}
    (hr : Stepper.runInstr instruction s = some t) :
    t.stack.length + pops instruction = s.stack.length + pushes instruction := by
  have hs : s.stack.length < 1024 := by
    by_contra hn
    simp [Stepper.runInstr, hn] at hr
  cases instruction with
  | push width value =>
      simp only [Stepper.runInstr, if_pos hs] at hr
      split at hr <;> simp only [Option.some.injEq] at hr <;> subst t <;>
        simp [pops, pushes]
  | op operation =>
    cases operation with
    | Dup n =>
      simp only [Stepper.runInstr, if_pos hs] at hr
      cases hg : s.stack[n.idx.val]? with
      | none => simp [hg] at hr
      | some value =>
        simp only [hg, Option.some.injEq] at hr
        subst t
        simp [pops, pushes, Operation.popArity, Operation.pushArity]
        omega
    | Swap n =>
      simp only [Stepper.runInstr, if_pos hs] at hr
      cases hg : s.stack.exchange 0 (n.idx.val + 1) with
      | none => simp [hg] at hr
      | some stack =>
        simp only [hg, Option.some.injEq] at hr
        subst t
        simp [pops, pushes, Operation.popArity, Operation.pushArity, exchange_length hg]
    | StopArith o | CompBit o | Env o | StackMemFlow o | System o =>
      cases o <;>
        rcases he : s.stack with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
        simp only [Stepper.runInstr, if_pos hs, he] at hr <;>
        (try contradiction) <;>
        (repeat' first
          | split at hr
          | (simp only [Option.some.injEq] at hr; subst t;
              simp_all [pops, pushes, Operation.popArity, Operation.pushArity])
          | contradiction)
    | Keccak o | Block o => cases o <;> simp [Stepper.runInstr, hs] at hr
    | Push o | DupN o | SwapN o | Exchange o | Log o =>
      simp [Stepper.runInstr, hs] at hr

#print axioms runInstr_length
end CycleSubmission.Global.StackPeak

namespace CycleSubmission.Global.StackPeak
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def peak {artifact : ProgramArtifact} {fork : Fork} :
    List (Stepper.Located artifact fork) → Nat
  | [] => 0
  | located :: rest => pushes located.instruction + peak rest - pops located.instruction

theorem runLocated_length {artifact : ProgramArtifact} {fork : Fork}
    {located : Stepper.Located artifact fork} {s t : State}
    (hr : Stepper.runLocated located s = some t) :
    t.stack.length + pops located.instruction =
      s.stack.length + pushes located.instruction := by
  unfold Stepper.runLocated at hr
  split at hr
  · exact runInstr_length hr
  · contradiction

theorem runLocatedBlock_append_peak {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State} (rho : List UInt256)
    (hcap : s.stack.length + rho.length + peak path < 1024)
    (hr : Stepper.runLocatedBlock path s = some t) :
    Stepper.runLocatedBlock path (CycleSubmission.Global.StackTail.append s rho) =
      some (CycleSubmission.Global.StackTail.append t rho) := by
  induction path generalizing s t with
  | nil =>
      simp only [Stepper.runLocatedBlock, Option.some.injEq] at hr
      subst t
      rfl
  | cons located rest ih =>
      cases hg : Stepper.runLocated located s with
      | none => simp [Stepper.runLocatedBlock, hg] at hr
      | some next =>
        have ha := CycleSubmission.Global.StackTail.runLocated_append rho (by omega) hg
        have hlen := runLocated_length hg
        have hnext : next.stack.length + rho.length + peak rest < 1024 := by
          simp only [peak] at hcap
          omega
        cases rest with
        | nil =>
          simp only [Stepper.runLocatedBlock, hg, Option.some.injEq] at hr
          subst t
          simp only [Stepper.runLocatedBlock, ha.1]
        | cons nextLocated tail =>
          cases hh : next.halt with
          | Running =>
            have hn : Stepper.runLocatedBlock (nextLocated :: tail) next = some t := by
              simpa only [Stepper.runLocatedBlock, hg, hh] using hr
            have hi := ih (s := next) hnext hn
            have hh' : (CycleSubmission.Global.StackTail.append next rho).halt = .Running := hh
            simpa only [Stepper.runLocatedBlock, ha.1, hh'] using hi
          | Success | Returned | Reverted | Exception error =>
              simp [Stepper.runLocatedBlock, hg, hh] at hr

def gasSteps {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) {s t : State} (rho : List UInt256)
    (hcap : s.stack.length + rho.length + peak path < 1024)
    (hr : Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = artifact.code) (hfork : s.fork = fork)
    (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (CycleSubmission.Global.StackTail.append s rho)
      (CycleSubmission.Global.StackTail.append t rho) :=
  Stepper.runLocatedBlock_sound artifact fork path hcode hfork
    (runLocatedBlock_append_peak path rho hcap hr) hrun hnp

#print axioms runLocatedBlock_append_peak
#print axioms gasSteps
end CycleSubmission.Global.StackPeak
namespace CycleSubmission.Global.StackPeak
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode

def peakInstructions : List Instr → Nat
  | [] => 0
  | i :: rest => pushes i + peakInstructions rest - pops i

theorem peak_eq {artifact : ProgramArtifact} {fork : Fork}
    (path : List (Stepper.Located artifact fork)) :
    peak path = peakInstructions (path.map Stepper.Located.instruction) := by
  induction path with
  | nil => rfl
  | cons i rest ih => simpa only [peak, List.map_cons, peakInstructions] using congrArg (fun v => pushes i.instruction + v - pops i.instruction) ih

def blockSteps_append {artifact : ProgramArtifact} {fork : Fork} {pc : Nat}
    {instructions : List Instr}
    (block : WindowTwentyOneBinding.Block artifact fork pc instructions)
    {s t : State} (env : WindowTwentyOneBinding.Environment artifact fork s)
    (hpc : s.pc = UInt256.ofNat pc)
    (hrun : WindowNibbleKernel.runInstructions instructions s = some t)
    (rho : List UInt256)
    (hcap : s.stack.length + rho.length + peakInstructions instructions < 1024) :
    GasSteps (CycleSubmission.Global.StackTail.append s rho)
      (CycleSubmission.Global.StackTail.append t rho) := by
  have hraw : WindowNibbleKernel.runInstructions (block.path.map Stepper.Located.instruction) s = some t := by
    rw [block.instructions_eq]
    exact hrun
  apply gasSteps block.path rho
    (by simpa only [peak_eq, block.instructions_eq] using hcap)
    (WindowTwentyOneLocated.run_linear block.path _ s t env.sizeBound block.layout hpc env.running hraw)
    env.code env.forkEq env.running env.noPrecompile

#print axioms blockSteps_append
end CycleSubmission.Global.StackPeak
