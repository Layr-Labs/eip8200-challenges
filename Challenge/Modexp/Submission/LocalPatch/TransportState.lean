import Challenge.Modexp.Submission.Isolation.Forward
import Challenge.Modexp.Submission.LocalPatch.LocalDecode
import Challenge.Modexp.Submission.LocalPatch.JumpDestLayout

set_option warningAsError true

/-!
State transport for the single-frame, account-insensitive MODEXP instruction
fragment. The public initial state has the deployed code in three places:
the active environment, the deployed account, and the original-account snapshot.
All three are changed here. No source account/code observation is being assumed
invariant. The supported opcode set is explicitly restricted in TransportDomain.

The candidate may have any nonnegative gas surplus and an independent execLength.
In this pinned semantics the supported StepRunning rules leave execLength alone.
-/
namespace Challenge.Modexp.Submission.LocalPatch.Transport

open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof

/-- The exact account map in the protected MODEXP initial state. -/
def deploymentAccounts (code : ByteArray) : AccountMap :=
  AccountMap.empty.set deployAddress { Account.empty with code := code }

/-- Change the single-frame code/world and retain all operational fields.
The source world is required to be the fixed reference world by Related.
This deliberately does not transport account/storage/code-observing opcodes. -/
def liftState (code : ByteArray) (credit counter : Nat) (s : State) : State :=
  { s with
    executionEnv := { s.executionEnv with code := code }
    accountMap := deploymentAccounts code
    substate := { s.substate with originalAccountMap := deploymentAccounts code }
    gasAvailable := s.gasAvailable + credit
    execLength := counter }

/-- Operational projection. Worlds are separately constrained by FixedWorld;
this is not an assertion that arbitrary account observations agree. -/
def erase (s : State) : State :=
  { s with
    executionEnv := { s.executionEnv with code := ByteArray.empty }
    accountMap := AccountMap.empty
    substate := { s.substate with originalAccountMap := AccountMap.empty }
    gasAvailable := 0
    execLength := 0 }

/-- The invariant at synchronized reference endpoints. -/
def FixedWorld (reference : ByteArray) (s : State) : Prop :=
  s.executionEnv.code = reference ∧
  s.accountMap = deploymentAccounts reference ∧
  s.substate.originalAccountMap = deploymentAccounts reference ∧
  s.callStack = []

/-- An explicit state relation, not a field requiring step equivalence. -/
def Related (reference candidate : ByteArray) (s t : State) : Prop :=
  FixedWorld reference s ∧
    ∃ credit counter : Nat, t = liftState candidate credit counter s

/-- Exception outputs cannot have a successful top-level suffix. -/
def NoException (s : State) : Prop :=
  ∀ e : ExecutionException, s.halt ≠ .Exception e

@[simp] theorem erase_lift (code : ByteArray) (credit counter : Nat) (s : State) :
    erase (liftState code credit counter s) = erase s := rfl

@[simp] theorem lift_code (code : ByteArray) (credit counter : Nat) (s : State) :
    (liftState code credit counter s).executionEnv.code = code := rfl

@[simp] theorem lift_gas (code : ByteArray) (credit counter : Nat) (s : State) :
    (liftState code credit counter s).gasAvailable = s.gasAvailable + credit := rfl

@[simp] theorem lift_counter (code : ByteArray) (credit counter : Nat) (s : State) :
    (liftState code credit counter s).execLength = counter := rfl

@[simp] theorem lift_result (code : ByteArray) (credit counter : Nat) (s : State) :
    (liftState code credit counter s).toResult = s.toResult := rfl

@[simp] theorem lift_done (code : ByteArray) (credit counter : Nat) (s : State) :
    (liftState code credit counter s).isDone = s.isDone := rfl

theorem lift_initial (reference candidate input : ByteArray) (gas credit : Nat) :
    liftState candidate credit 0 (initialState reference input gas) =
      initialState candidate input (gas + credit) := rfl

theorem related_entry (reference candidate input : ByteArray) (gas : Nat) :
    Related reference candidate (initialState reference input gas)
      (initialState candidate input gas) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, 0, 0, ?_⟩
  exact (lift_initial reference candidate input gas 0).symm

/-- Finite local byte-window equality supplies full fork-filtered decoding. -/
theorem decoded_lift {code : ByteArray} {credit counter : Nat} {s : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true) :
    (liftState code credit counter s).decoded = s.decoded := by
  have h := LocalDecode.decodeAt_eq_of_checkAt hwindow
  simp only [State.decoded, liftState, State.fork]
  rw [← h]
  rfl

theorem decodedOp_lift {code : ByteArray} {credit counter : Nat} {s : State}
    (hwindow : LocalDecode.checkAt s.executionEnv.code code s.pc.toNat = true) :
    (liftState code credit counter s).decodedOp = s.decodedOp := by
  exact congrArg (fun d => d.map Prod.fst) (decoded_lift (credit := credit)
    (counter := counter) hwindow)

/-- Do not rewrite Nat subtraction without the original affordability premise. -/
theorem subtract_credit (credit : Nat) {gas cost : Nat} (hcost : cost ≤ gas) :
    gas + credit - cost = (gas - cost) + credit := by omega

theorem afford_credit (credit : Nat) {gas cost : Nat} (hcost : cost ≤ gas) :
    cost ≤ gas + credit := by omega

/-- A genuinely halted empty-call-stack state admits no intervening step. -/
theorem eval_result_of_done {s : State} {result : ExecutionResult}
    (hhalt : s.halt ≠ .Running) (hstack : s.callStack = [])
    (heval : Eval s result) : result = s.toResult := by
  cases heval with
  | halted _ _ => rfl
  | stepThen hstep _ => exact (Step.not_from_done hstep hhalt hstack).elim

theorem noException_of_successful {s : State}
    (hstack : s.callStack = [])
    (hsuffix : ∃ output : ByteArray, Eval s (.returned output)) : NoException s := by
  intro e he
  obtain ⟨output, heval⟩ := hsuffix
  have hh : s.halt ≠ .Running := by rw [he]; intro h; cases h
  have hr := eval_result_of_done hh hstack heval
  rw [State.toResult_exception s e he] at hr
  cases hr

/-- The synchronized relation discharges ForwardRefinement.finish without any
unproved instruction transport or equal-gas assumption. -/
theorem related_finish {reference candidate : ByteArray} {s t : State}
    {output : ByteArray} (hrel : Related reference candidate s t)
    (hhalt : s.halt ≠ .Running) (hstack : s.callStack = [])
    (hresult : s.toResult = .returned output) :
    ∃ final : State, Steps t final ∧ final.halt ≠ .Running ∧
      final.callStack = [] ∧ final.toResult = .returned output := by
  obtain ⟨_, credit, counter, rfl⟩ := hrel
  exact ⟨liftState candidate credit counter s, Steps.refl _, hhalt, hstack, hresult⟩

end Challenge.Modexp.Submission.LocalPatch.Transport
