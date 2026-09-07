import Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityFragmentChain

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityStackEffect

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTemplate StackRoundTrace

/-- Net stack growth, used only with the certified pure opcode subset. -/
def delta : Instr → Int
  | .push _ _ => 1
  | .op (.Dup _) => 1
  | .op .ADD | .op .AND | .op .OR | .op .XOR | .op .SHL | .op .SHR
  | .op .POP | .op .SUB | .op .MUL => -1
  | _ => 0

def total : List Instr → Int
  | [] => 0
  | instruction :: rest => delta instruction + total rest

private theorem exchange_length {α : Type} {before after : List α} {i j : Nat}
    (h : before.exchange i j = some after) : after.length = before.length := by
  unfold List.exchange at h
  cases hi : before[i]? <;> simp [hi] at h
  cases hj : before[j]? <;> simp [hj] at h
  subst after
  simp

theorem runInstr_length_straight {instruction : Instr}
    (hform : StraightLine instruction) {s t : State}
    (hresult : Stepper.runInstr instruction s = some t) :
    (t.stack.length : Int) = (s.stack.length : Int) + delta instruction := by
  cases hform <;> unfold Stepper.runInstr at hresult
  all_goals repeat' first | split at hresult | simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst t
  all_goals simp_all [delta, List.length_cons]
  all_goals apply exchange_length; assumption

theorem runInstr_length {instruction : Instr}
    (hform : PairMultiplyLift.Advances instruction) {s t : State}
    (hresult : Stepper.runInstr instruction s = some t) :
    (t.stack.length : Int) = (s.stack.length : Int) + delta instruction := by
  rcases hform with (hstraight | hsub | hjumpdest) | hmul
  · exact runInstr_length_straight hstraight hresult
  all_goals subst instruction; unfold Stepper.runInstr at hresult
  all_goals repeat' first | split at hresult | simp_all only [Option.some.injEq, reduceCtorEq]
  all_goals subst t
  all_goals simp_all [delta, List.length_cons]

/-- A successful prefix fixes its exact stack height independently of values,
memory, PC, or the arithmetic expression computed by that prefix. -/
theorem runInstrSeq_length (code : List Instr)
    (hform : ∀ instruction ∈ code, PairMultiplyLift.Advances instruction)
    {s t : State} (hresult : runInstrSeq code s = some t) :
    (t.stack.length : Int) = (s.stack.length : Int) + total code := by
  induction code generalizing s with
  | nil =>
      cases hresult
      simp [total]
  | cons instruction rest ih =>
      have hfirst := hform instruction (by simp)
      have hrest : ∀ i ∈ rest, PairMultiplyLift.Advances i := by
        intro i hi
        exact hform i (by simp [hi])
      cases hstep : Stepper.runInstr instruction s with
      | none => simp [runInstrSeq, hstep] at hresult
      | some next =>
          have hlen := runInstr_length hfirst hstep
          cases rest with
          | nil =>
              have heq : next = t := by simpa [runInstrSeq, hstep] using hresult
              simpa [heq, total] using hlen
          | cons a tail =>
              cases hhalt : next.halt <;> simp [runInstrSeq, hstep, hhalt] at hresult
              have htail := ih hrest hresult
              simp only [total] at *
              omega

theorem cap_of_total (code : List Instr)
    (hform : ∀ instruction ∈ code, PairMultiplyLift.Advances instruction)
    {s : State} (hbound : (s.stack.length : Int) + total code < 1023) :
    ∀ middle, runInstrSeq code s = some middle → middle.stack.length < 1023 := by
  intro middle hresult
  have hlen := runInstrSeq_length code hform hresult
  omega

#print axioms runInstr_length
#print axioms runInstrSeq_length
#print axioms cap_of_total

end Challenge.Ripemd160.Submission.Proofs.Bytecode.CavityStackEffect
