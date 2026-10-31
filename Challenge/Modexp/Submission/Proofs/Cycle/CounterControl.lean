import Challenge.Modexp.Submission.Proofs.Cycle.LoopBlocks
import Challenge.Modexp.Submission.Proofs.Cycle.EntryBinding
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.CounterControl
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.NormalizeMeaning CycleSubmission.Execution
open HistoricalSearch.CRTControl
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def counter (s : State) : UInt256 := s.stack.getD 14 (UInt256.ofNat 0)
def dec (c : UInt256) : UInt256 := c - UInt256.ofNat 1
def initial (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 7619, stack := frame a n (n 0) (n 1) (counter s :: rest)}
def tested (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 7645, stack := UInt256.ofNat 5694 :: counter s :: frame a n (n 0) (n 1) (dec (counter s) :: rest)}
def branched (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := if (counter s).toNat = 0 then UInt256.ofNat 7646 else UInt256.ofNat 5694, stack := frame a n (n 0) (n 1) (dec (counter s) :: rest)}
def looped (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5694, stack := frame a n (n 0) (n 1) (dec (counter s) :: rest)}
def repeated (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 5695, stack := frame a n (n 0) (n 1) (dec (counter s) :: rest)}
def completed (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  if (counter s).toNat = 0 then
    {s with pc := UInt256.ofNat 7652, stack := frame a n (n 0) (n 1) (dec (counter s) :: rest)}
  else repeated s a n rest

theorem head_run (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions counterHeadProgram (initial s a n rest) = some (tested s a n rest) :=
  counterHead_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) (n 1) mask (n 0) (n 3) (a 8) (counter s) rest hcap hact

noncomputable def decision (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (initial s a n rest) (branched s a n rest) := by
  have h1 := LoopBlocks.counterBlock.steps (s := initial s a n rest)
    (env.transfer rfl rfl) rfl (head_run s a n rest hcap hact)
  have valid : Decode.isValidJumpDest (tested s a n rest).executionEnv.code 5694 = true := by
    rw [show (tested s a n rest).executionEnv.code = Artifact.bytecode from env.code]
    exact LoopBlocks.validJump6152
  have cap : (tested s a n rest).stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hr := jumpi_run (tested s a n rest) (UInt256.ofNat 5694) (counter s)
    (frame a n (n 0) (n 1) (dec (counter s) :: rest)) rfl cap valid
  have h2 := LoopBlocks.counterJumpBlock.steps (s := tested s a n rest)
    (env.transfer rfl rfl) rfl hr
  have he : conditionalModel (tested s a n rest) = branched s a n rest := by
    by_cases hz : (counter s).toNat = 0
    · simp [conditionalModel, tested, branched, hz]
      rfl
    · simp [conditionalModel, tested, branched, hz]
  rw [he] at h2
  exact h1.trans h2

noncomputable def repeatSteps (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s) (hcap : rest.length ≤ 959) :
    GasSteps (looped s a n rest) (repeated s a n rest) := by
  have hd := jumpDest_run (looped s a n rest) (by
    simp only [looped, frame, List.length_cons, List.length_append, List.length_nil]
    omega)
  exact EntryBinding.headBlock.steps (s := looped s a n rest) (env.transfer rfl rfl) rfl hd

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 959) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (initial s a n rest) (completed s a n rest) := by
  have h := decision s a n rest env hcap hact
  by_cases hz : (counter s).toNat = 0
  · have hb : branched s a n rest =
        {s with pc := UInt256.ofNat 7646, stack := frame a n (n 0) (n 1) (dec (counter s) :: rest)} := by
      simp only [branched, if_pos hz]
    rw [hb] at h
    have hx := LoopBlocks.counterExitBlock.steps
      (s := {s with pc := UInt256.ofNat 7646, stack := frame a n (n 0) (n 1) (dec (counter s) :: rest)})
      (env.transfer rfl rfl) rfl
      (counterExit_run s (frame a n (n 0) (n 1) (dec (counter s) :: rest)) (by
        simp only [frame, List.length_cons, List.length_append, List.length_nil]; omega))
    simp only [completed, if_pos hz]
    exact h.trans hx
  · have hb : branched s a n rest = looped s a n rest := by
      simp only [branched, looped, if_neg hz]
    rw [hb] at h
    simp only [completed, if_neg hz]
    exact h.trans (repeatSteps s a n rest env hcap)

theorem memory_written (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).memory = s.memory := by
  unfold completed
  split_ifs <;> rfl

theorem memory_output (s : State) (a b n : Nat → UInt256) (inv : UInt256) (rest : List UInt256)
    (h : SquareMeaning.Memory0 s.memory inv a b n) :
    SquareMeaning.Memory0 (completed s a n rest).memory inv a b n := by
  rw [memory_written]
  exact h

theorem executionEnv_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).executionEnv = s.executionEnv := by
  unfold completed
  split_ifs <;> rfl
theorem halt_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).halt = s.halt := by
  unfold completed
  split_ifs <;> rfl
theorem active_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).activeWords = s.activeWords := by
  unfold completed
  split_ifs <;> rfl
theorem counter_value (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    counter (completed s a n rest) = dec (counter s) := by
  unfold completed
  split_ifs <;> rfl

theorem frame_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).stack = frame a n (n 0) (n 1) (counter (completed s a n rest) :: rest) := by
  rw [counter_value]
  unfold completed
  split_ifs <;> rfl

theorem keeps_low (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (start count : Nat) (he : start+count ≤ 1728) :
    MachineState.readPadded (completed s a n rest).memory start count =
      MachineState.readPadded s.memory start count := by
  rw [memory_written]

theorem calls_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).callStack = s.callStack := by
  unfold completed
  split_ifs <;> rfl

end CycleSubmission.CounterControl
