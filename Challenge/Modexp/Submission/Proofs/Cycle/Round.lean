import Challenge.Modexp.Submission.Proofs.Cycle.SquareStep
import Challenge.Modexp.Submission.Proofs.Cycle.CounterControl
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.Round
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.SquareStep (zeroWords digits)

def result (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  CounterControl.completed (SquareStep.result s inv a n (CounterControl.counter s :: rest)) (digits inv a n) n rest

theorem counter_middle (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    CounterControl.counter (SquareStep.result s inv a n (CounterControl.counter s :: rest)) = CounterControl.counter s := by
  rw [CounterControl.counter, SquareStep.frame_output]
  rfl


theorem reset_middle (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    CounterControl.initial (SquareStep.result s inv a n (CounterControl.counter s :: rest)) (digits inv a n) n rest =
      SquareStep.result s inv a n (CounterControl.counter s :: rest) := by
  unfold CounterControl.initial
  rw [counter_middle]
  exact SquareExecution.reset_self _ _ _ (SquareStep.pc_output s inv a n (CounterControl.counter s :: rest))
    (SquareStep.frame_output s inv a n (CounterControl.counter s :: rest))

noncomputable def gasSteps (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : SquareMeaning.Memory0 s.memory inv a zeroWords n)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 5695, stack := SquareMeaning.frame0 inv a zeroWords n (CounterControl.counter s :: rest)}
      (result s inv a n rest) := by
  have h1 := SquareStep.gasSteps s inv a n (CounterControl.counter s :: rest) env h (by simp only [List.length_cons]; omega) hact
  have e := env.transfer (SquareStep.executionEnv_eq s inv a n (CounterControl.counter s :: rest)) (SquareStep.halt_eq s inv a n (CounterControl.counter s :: rest))
  have act : 88 ≤ (SquareStep.result s inv a n (CounterControl.counter s :: rest)).activeWords.toNat := by
    rw [SquareStep.active_eq]; exact hact
  have h2 := CounterControl.gasSteps (SquareStep.result s inv a n (CounterControl.counter s :: rest)) (digits inv a n) n rest e hcap act
  have he := reset_middle s inv a n rest
  rw [he] at h2
  exact h1.trans h2

theorem memory_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (h : SquareMeaning.Memory0 s.memory inv a zeroWords n) :
    SquareMeaning.Memory0 (result s inv a n rest).memory inv (digits inv a n) zeroWords n := by
  unfold result
  rw [CounterControl.memory_written]
  exact SquareStep.memory_output s inv a n (CounterControl.counter s :: rest) h

theorem frame_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).stack = SquareMeaning.frame0 inv (digits inv a n) zeroWords n (CounterControl.counter (result s inv a n rest) :: rest) :=
  CounterControl.frame_eq (SquareStep.result s inv a n (CounterControl.counter s :: rest)) (digits inv a n) n rest

theorem executionEnv_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).executionEnv = s.executionEnv := by
  unfold result
  rw [CounterControl.executionEnv_eq, SquareStep.executionEnv_eq]

theorem halt_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).halt = s.halt := by
  unfold result
  rw [CounterControl.halt_eq, SquareStep.halt_eq]

theorem active_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).activeWords = s.activeWords := by
  unfold result
  rw [CounterControl.active_eq, SquareStep.active_eq]

theorem pc_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (k : Nat) (hk : 1 ≤ k) (hk16 : k ≤ 16)
    (hc : CounterControl.counter s = UInt256.ofNat (k-1)) :
    (result s inv a n rest).pc = if k = 1 then UInt256.ofNat 7652 else UInt256.ofNat 5695 := by
  unfold result CounterControl.completed
  rw [counter_middle, hc]
  interval_cases k <;> rfl

theorem counter_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (k : Nat) (hk : 1 < k) (hk16 : k ≤ 16)
    (hc : CounterControl.counter s = UInt256.ofNat (k-1)) :
    CounterControl.counter (result s inv a n rest) = UInt256.ofNat (k-2) := by
  have hz : (CounterControl.counter (SquareStep.result s inv a n (CounterControl.counter s :: rest))).toNat ≠ 0 := by
    rw [counter_middle, hc]
    interval_cases k <;> decide
  rw [result, CounterControl.counter_value, counter_middle, hc]
  interval_cases k <;> rfl

theorem keeps_base (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (start count : Nat) (hs : 256 ≤ start) (he : start+count ≤ 768) :
    MachineState.readPadded (result s inv a n rest).memory start count =
      MachineState.readPadded s.memory start count := by
  unfold result
  rw [CounterControl.memory_written]
  exact SquareStep.keeps_base s inv a n (CounterControl.counter s :: rest) start count hs he

theorem calls_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    (result s inv a n rest).callStack = s.callStack := by
  unfold result
  rw [CounterControl.calls_eq, SquareStep.calls_eq]

end CycleSubmission.Round
