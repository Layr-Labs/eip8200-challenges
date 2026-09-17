import Challenge.Modexp.Submission.LocalPatch.StaticExecution
import Challenge.Modexp.Submission.LocalPatch.StaticDomainFrontier64
import Challenge.Modexp.Spec

set_option warningAsError true

/-!
# Actual frontier64 execution stays inside the certified static domain

This module instantiates `StaticExecution` for the exact frozen frontier64 bytecode.
It proves a PC/decode invariant for every finite actual execution prefix from
the MODEXP initial state.  It does not prove output correctness, gas
refinement, or equivalence to a different candidate.
-/

namespace Challenge.Modexp.Submission.LocalPatch.StaticExecutionFrontier64

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.LocalPatch.StaticDomain
open Challenge.Modexp.Submission.LocalPatch.StaticExecution
open Challenge.Modexp.Submission.LocalPatch.StaticDomainFrontier64

abbrev code : ByteArray := StaticDomainFrontier64.code
abbrev cert : Certificate code := StaticDomainFrontier64.certificate

def initialEnv (calldata : ByteArray) : ExecutionEnv :=
  (Challenge.Modexp.initialState code calldata 0).executionEnv

@[simp] theorem initialEnv_code (calldata : ByteArray) :
    (initialEnv calldata).code = code := rfl

@[simp] theorem initialEnv_fork (calldata : ByteArray) :
    (initialEnv calldata).fork = .Osaka := rfl

private theorem code_size_lt : code.size < 2 ^ 256 := by
  rw [Challenge.Modexp.submissionBytecode_size]
  norm_num

/-- The exact MODEXP initial state is the live entry of the certified domain. -/
theorem initial_inDomain (calldata : ByteArray) (gas : Nat) :
    InDomain cert (initialEnv calldata)
      (Challenge.Modexp.initialState code calldata gas) := by
  refine Or.inr ⟨rfl, rfl, rfl, ?_⟩
  change UInt256.toNat (UInt256.ofNat 0) ∈ cert.pcs
  simpa using cert.entry

/-- Every finite actual execution prefix is either top-level terminal or is a
live same-environment state at one of the 4,393 certified PCs. -/
theorem steps_inDomain (calldata : ByteArray) (gas : Nat) {t : State}
    (hsteps : Steps (Challenge.Modexp.initialState code calldata gas) t) :
    InDomain cert (initialEnv calldata) t :=
  Challenge.Modexp.Submission.LocalPatch.StaticExecution.inDomain_steps
    cert code_size_lt
    (initialEnv_code calldata) (initialEnv_fork calldata)
    (initial_inDomain calldata gas) hsteps

/-- Concrete running-state corollary used by ordinary-step transport.
Every running endpoint of an actual frontier64 prefix has the original environment,
empty caller stack, certified PC, and an actually available supported decode. -/
theorem running_endpoint (calldata : ByteArray) (gas : Nat) {t : State}
    (hsteps : Steps (Challenge.Modexp.initialState code calldata gas) t)
    (htRunning : t.halt = .Running) :
    t.callStack = [] ∧
      t.executionEnv = initialEnv calldata ∧
      t.fork = .Osaka ∧
      t.executionEnv.code = code ∧
      t.pc.toNat ∈ cert.pcs ∧
      ∃ op imm, t.decoded = some (op, imm) ∧ transportSafe op = true := by
  have hinv := steps_inDomain calldata gas hsteps
  rcases hinv with hterminal | hrunning
  · exact False.elim (hterminal.1 htRunning)
  · have hdecoded :=
      Challenge.Modexp.Submission.LocalPatch.StaticExecution.decoded_of_runningInDomain
        cert (initialEnv_code calldata) (initialEnv_fork calldata) hrunning
    rcases hrunning with ⟨_, htEmpty, htEnv, htPC⟩
    have htFork : t.fork = .Osaka := by
      change t.executionEnv.fork = .Osaka
      rw [htEnv]
      exact initialEnv_fork calldata
    have htCode : t.executionEnv.code = code := by
      rw [htEnv]
      exact initialEnv_code calldata
    exact ⟨htEmpty, htEnv, htFork, htCode, htPC, hdecoded⟩

/-- A one-step form convenient for the frozen-reference side of a refinement
proof. -/
theorem step_from_running_endpoint
    (calldata : ByteArray) (gas : Nat) {s t : State}
    (hprefix : Steps (Challenge.Modexp.initialState code calldata gas) s)
    (hsRunning : s.halt = .Running)
    (hstep : Step s t) :
    TerminalTop t ∨
      (t.halt = .Running ∧
        t.callStack = [] ∧
        t.executionEnv = s.executionEnv ∧
        StaticSuccessor code s.pc.toNat t.pc.toNat) := by
  obtain ⟨hsEmpty, hsEnv, hsFork, hsCode, hsPC, _⟩ :=
    running_endpoint calldata gas hprefix hsRunning
  exact Challenge.Modexp.Submission.LocalPatch.StaticExecution.step_outcome
    cert code_size_lt hstep hsRunning hsEmpty hsCode hsFork hsPC

end Challenge.Modexp.Submission.LocalPatch.StaticExecutionFrontier64
