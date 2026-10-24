import Challenge.Modexp.Submission.Proofs.Cycle.LoopBlocks
import Challenge.Modexp.Submission.Proofs.Cycle.EntryBinding
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.CounterControl
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof Challenge.EvmProof.Word
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.NormalizeMeaning CycleSubmission.Execution
open HistoricalSearch.CRTControl
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def counter (s : State) : UInt256 := MachineState.readWord s.memory 1728
def initial (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 8085, stack := frame a n (n 0) (n 1) rest}
def tested (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 8094
    stack := UInt256.ofNat 8110 :: UInt256.isZero (counter s) :: frame a n (n 0) (n 1) rest}
def branched (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := if (counter s).toNat = 0 then UInt256.ofNat 8110 else UInt256.ofNat 8095
    stack := frame a n (n 0) (n 1) rest}
def decremented (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 8109
    memory := MachineState.writeBytes s.memory (Data.Bytes.natToBytesPadded (counter s - UInt256.ofNat 1).toNat 32) 1728
    stack := UInt256.ofNat 6152 :: frame a n (n 0) (n 1) rest}
def repeated (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {decremented s a n rest with pc := UInt256.ofNat 6153, stack := frame a n (n 0) (n 1) rest}
def completed (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  if (counter s).toNat = 0 then {s with pc := UInt256.ofNat 8110, stack := frame a n (n 0) (n 1) rest}
  else repeated s a n rest

theorem head_run (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions counterHeadProgram (initial s a n rest) = some (tested s a n rest) :=
  counterHead_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) (n 1) mask (n 0) (n 3) (a 8) rest hcap hact

noncomputable def decision (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (initial s a n rest) (branched s a n rest) := by
  have h1 := LoopBlocks.counterBlock.steps (s := initial s a n rest)
    (env.transfer rfl rfl) rfl (head_run s a n rest hcap hact)
  have valid : Decode.isValidJumpDest (tested s a n rest).executionEnv.code 8110 = true := by
    rw [show (tested s a n rest).executionEnv.code = Artifact.bytecode from env.code]
    exact LoopBlocks.validJump8110
  have cap : (tested s a n rest).stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hr := jumpi_run (tested s a n rest) (UInt256.ofNat 8110) (UInt256.isZero (counter s))
    (frame a n (n 0) (n 1) rest) rfl cap valid
  have h2 := LoopBlocks.counterJumpBlock.steps (s := tested s a n rest)
    (env.transfer rfl rfl) rfl hr
  have he : conditionalModel (tested s a n rest) = branched s a n rest := by
    by_cases hz : (counter s).toNat = 0
    · simp [conditionalModel, tested, branched, word_toNat_isZero, hz]
    · simp [conditionalModel, tested, branched, word_toNat_isZero, hz]
      rfl
  rw [he] at h2
  exact h1.trans h2

noncomputable def repeatSteps (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps {s with pc := UInt256.ofNat 8095, stack := frame a n (n 0) (n 1) rest}
      (repeated s a n rest) := by
  have hr := decrement_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) (n 1) mask (n 0) (n 3) (a 8) rest hcap hact
  have h1 := LoopBlocks.decrementBlock.steps
    (s := {s with pc := UInt256.ofNat 8095, stack := frame a n (n 0) (n 1) rest})
    (env.transfer rfl rfl) rfl hr
  have valid : Decode.isValidJumpDest (decremented s a n rest).executionEnv.code 6152 = true := by
    rw [show (decremented s a n rest).executionEnv.code = Artifact.bytecode from env.code]
    exact LoopBlocks.validJump6152
  have cap : (decremented s a n rest).stack.length < 1024 := by
    simp only [decremented, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hj := jump_run (decremented s a n rest) (UInt256.ofNat 6152)
    (frame a n (n 0) (n 1) rest) rfl cap valid
  have h2 := LoopBlocks.repeatJumpBlock.steps (s := decremented s a n rest)
    (env.transfer rfl rfl) rfl hj
  have hd := jumpDest_run (jumpModel (decremented s a n rest)) (by
    simp only [jumpModel, decremented, List.drop_succ_cons, List.drop_zero,
      frame, List.length_cons, List.length_append, List.length_nil]
    omega)
  have h3 := EntryBinding.headBlock.steps (s := jumpModel (decremented s a n rest))
    (env.transfer rfl rfl) rfl hd
  exact h1.trans (h2.trans h3)

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (initial s a n rest) (completed s a n rest) := by
  have h := decision s a n rest env hcap hact
  by_cases hz : (counter s).toNat = 0
  · simpa only [completed, branched, if_pos hz] using h
  · simp only [branched, if_neg hz] at h
    simp only [completed, if_neg hz]
    exact h.trans (repeatSteps s a n rest env hcap hact)

theorem memory_output (s : State) (a b n : Nat → UInt256) (inv : UInt256) (rest : List UInt256)
    (h : SquareMeaning.Memory0 s.memory inv a b n) :
    SquareMeaning.Memory0 (completed s a n rest).memory inv a b n := by
  by_cases hz : (counter s).toNat = 0
  · simpa only [completed, if_pos hz] using h
  · simp only [completed, if_neg hz]
    constructor <;>
      simp (disch := decide) only [repeated, decremented, readStore,
        h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600,
        h.at32, h.at64, h.at96, h.at128, h.at160]

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
theorem frame_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).stack = frame a n (n 0) (n 1) rest := by
  unfold completed
  split_ifs <;> rfl

theorem counter_value (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (hz : (counter s).toNat ≠ 0) :
    counter (completed s a n rest) = counter s - UInt256.ofNat 1 := by
  rw [completed, if_neg hz]
  simp only [counter, repeated, decremented, Challenge.EvmProof.Memory.readWord_writeWord]

theorem keeps_low (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (start count : Nat) (he : start+count ≤ 1728) :
    MachineState.readPadded (completed s a n rest).memory start count =
      MachineState.readPadded s.memory start count := by
  unfold completed
  split_ifs
  · rfl
  · apply Challenge.EvmProof.Memory.readPadded_writeBytes_disjoint
    exact Or.inl he

theorem calls_eq (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).callStack = s.callStack := by
  unfold completed
  split_ifs <;> rfl

end CycleSubmission.CounterControl
