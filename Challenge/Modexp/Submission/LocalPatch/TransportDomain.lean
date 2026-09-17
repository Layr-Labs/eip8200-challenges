import Challenge.Modexp.Submission.LocalPatch.TransportState

set_option warningAsError true
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.LocalPatch.Transport

open EvmSemantics EvmSemantics.EVM

/-- STOP is handled by the terminal/control family. -/
def arithmetic : Operation → Bool
  | .StopArith .STOP => false
  | .StopArith _ => true
  | _ => false

def bitwise : Operation → Bool
  | .CompBit _ => true
  | _ => false

def stackOps : Operation → Bool
  | .Push _ | .Dup _ | .Swap _ | .DupN _ | .SwapN _ | .Exchange _ => true
  | .StackMemFlow .POP => true
  | _ => false

def memoryInput : Operation → Bool
  | .StackMemFlow .MLOAD | .StackMemFlow .MSTORE | .StackMemFlow .MSTORE8
  | .StackMemFlow .MSIZE | .StackMemFlow .MCOPY => true
  | .Env .CALLDATALOAD | .Env .CALLDATASIZE | .Env .CALLDATACOPY => true
  | _ => false

def control : Operation → Bool
  | .StopArith .STOP => true
  | .StackMemFlow .JUMP | .StackMemFlow .JUMPI | .StackMemFlow .JUMPDEST
  | .StackMemFlow .PC => true
  | .System .RETURN => true
  | _ => false

def ordinary (op : Operation) : Bool :=
  arithmetic op || bitwise op || stackOps op || memoryInput op || control op

/-- This is a check on the actual fork-filtered decoded operation. It is not
an assertion that a transition or a whole-program simulation exists. -/
def Has (family : Operation → Bool) (s : State) : Prop :=
  (match s.decodedOp with
   | none => false
   | some op => family op) = true

theorem ordinary_cases {s : State} (h : Has ordinary s) :
    Has arithmetic s ∨ Has bitwise s ∨ Has stackOps s ∨
      Has memoryInput s ∨ Has control s := by
  cases hd : s.decodedOp with
  | none => simp [Has, hd] at h
  | some op => simpa [Has, hd, ordinary, or_assoc] using h

/-- All support decisions are independent of the candidate bytes. -/
example : ordinary .GAS = false := rfl
example : ordinary .CODESIZE = false := rfl
example : ordinary .CODECOPY = false := rfl
example : ordinary .EXTCODEHASH = false := rfl
example : ordinary .SLOAD = false := rfl
example : ordinary .CALL = false := rfl

private theorem false_of_has_not_ordinary {s : State} {op : Operation}
    (hallowed : Has ordinary s) (hdecode : s.decodedOp = some op)
    (hop : ordinary op = false) : False := by
  have hf : false = true := by
    simpa only [Has, hdecode, hop] using hallowed
  cases hf

private theorem ordinary_executionEnv {s t : State} (hstep : StepRunning s t)
    (hallowed : Has ordinary s) : t.executionEnv = s.executionEnv := by
  cases hstep
  case call =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case callcode =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case delegatecall =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case staticcall =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create2 =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  all_goals rfl

private theorem ordinary_accountMap {s t : State} (hstep : StepRunning s t)
    (hallowed : Has ordinary s) : t.accountMap = s.accountMap := by
  cases hstep
  case sstore =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case tstore =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case call =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case callcode =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case createCollision =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create2Collision =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create2 =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case selfDestruct =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  all_goals rfl

private theorem ordinary_substate {s t : State} (hstep : StepRunning s t)
    (hallowed : Has ordinary s) : t.substate = s.substate := by
  cases hstep
  case balance =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case extcodesize =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case extcodecopy =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case extcodehash =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case sload =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case sstore =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case call =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case callFail =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case callcode =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case callcodeFail =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case delegatecall =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case delegatecallFail =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case staticcall =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case staticcallFail =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create2 =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case selfDestruct =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case log =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  all_goals rfl

private theorem ordinary_callStack {s t : State} (hstep : StepRunning s t)
    (hallowed : Has ordinary s) : t.callStack = s.callStack := by
  cases hstep
  case call =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case callcode =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case delegatecall =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case staticcall =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  case create2 =>
    exact (false_of_has_not_ordinary hallowed (by assumption) (by rfl)).elim
  all_goals rfl

private theorem ordinary_execLength {s t : State} (hstep : StepRunning s t)
    (_hallowed : Has ordinary s) : t.execLength = s.execLength := by
  cases hstep <;> rfl

/-- This is an actual inversion proof of the pinned StepRunning relation.
Unsupported account/call/create/log cases are contradicted by their decoding
premise; ordinary success and exception cases preserve this context by rfl. -/
theorem ordinary_context {s t : State} (hstep : StepRunning s t)
    (hallowed : Has ordinary s) :
    t.executionEnv = s.executionEnv ∧ t.accountMap = s.accountMap ∧
      t.substate = s.substate ∧ t.callStack = s.callStack ∧
      t.execLength = s.execLength := by
  exact ⟨ordinary_executionEnv hstep hallowed,
    ordinary_accountMap hstep hallowed,
    ordinary_substate hstep hallowed,
    ordinary_callStack hstep hallowed,
    ordinary_execLength hstep hallowed⟩

theorem fixedWorld_next {reference : ByteArray} {s t : State}
    (hw : FixedWorld reference s) (hstep : StepRunning s t)
    (hallowed : Has ordinary s) : FixedWorld reference t := by
  obtain ⟨he, ha, hs, hc, _⟩ := ordinary_context hstep hallowed
  rcases hw with ⟨hcode, hacc, horig, hcall⟩
  exact ⟨by rw [he]; exact hcode, ha.trans hacc,
    by rw [hs]; exact horig, hc.trans hcall⟩

end Challenge.Modexp.Submission.LocalPatch.Transport
