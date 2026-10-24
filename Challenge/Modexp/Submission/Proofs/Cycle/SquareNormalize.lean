import Challenge.Modexp.Submission.Proofs.Cycle.LoopBlocks
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeBinding
import Challenge.Modexp.Submission.Proofs.Cycle.ControlArithmetic
import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace CycleSubmission.SquareNormalize
open EvmSemantics EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBinding
open CycleSubmission.NormalizeMeaning CycleSubmission.ControlArithmetic
open CycleSubmission.Execution
open HistoricalSearch.CRTControl HistoricalSearch.CRTMemoryCells
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def initial (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with pc := UInt256.ofNat 8077, stack := frame a n (n 0) (n 1) rest}
def tested (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 8084
    stack := UInt256.ofNat 11008 :: overflowFlag a :: frame a n (n 0) (n 1) rest}
def branched (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := if (overflowFlag a).toNat = 0 then UInt256.ofNat 8085 else UInt256.ofNat 11008
    stack := frame a n (n 0) (n 1) rest}
def completed (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  if (overflowFlag a).toNat = 0 then
    {s with pc := UInt256.ofNat 8085, stack := frame a n (n 0) (n 1) rest}
  else NormalizeBinding.returned s a n (UInt256.ofNat 8085) (n 1) rest

theorem head_run (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions overflowHeadProgram (initial s a n rest) = some (tested s a n rest) := by
  exact overflowHead_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
    (n 8) (n 1) mask (n 0) (n 3) (a 8) rest hcap hact

noncomputable def decision (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (initial s a n rest) (branched s a n rest) := by
  have h1 := LoopBlocks.overflowBlock.steps (s := initial s a n rest)
    (env.transfer rfl rfl) rfl (head_run s a n rest hcap hact)
  have valid : Decode.isValidJumpDest (tested s a n rest).executionEnv.code 11008 = true := by
    rw [show (tested s a n rest).executionEnv.code = Artifact.bytecode from env.code]
    exact LoopBlocks.validJump11008
  have cap : (tested s a n rest).stack.length < 1024 := by
    simp only [tested, frame, List.length_cons, List.length_append, List.length_nil]
    omega
  have hr := jumpi_run (tested s a n rest) (UInt256.ofNat 11008) (overflowFlag a)
    (frame a n (n 0) (n 1) rest) rfl cap valid
  have h2 := LoopBlocks.overflowJumpBlock.steps (s := tested s a n rest)
    (env.transfer rfl rfl) rfl hr
  exact h1.trans h2

noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (env : Environment Artifact.artifact .Osaka s)
    (h : MemoryInput s.memory a n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    GasSteps (initial s a n rest) (completed s a n rest) := by
  have hd := decision s a n rest env hcap hact
  by_cases hz : (overflowFlag a).toNat = 0
  · simpa only [completed, branched, if_pos hz] using hd
  · have prep := normalizesquare_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7) modulusP
      (n 8) (n 1) mask (n 0) (n 3) (a 8) rest hcap hact
    have hp := LoopBlocks.normalizesquareBlock.steps
      (s := {s with pc := UInt256.ofNat 11008, stack := frame a n (n 0) (n 1) rest})
      (env.transfer rfl rfl) rfl prep
    have hn := NormalizeBinding.gasSteps s a n (UInt256.ofNat 8085) (n 1) rest env h hcap hact
      NormalizeBinding.validJump8085
    have hc := hp.trans hn
    simp only [branched, if_neg hz] at hd
    simp only [completed, if_neg hz]
    exact hd.trans hc

theorem memory_output (s : State) (a b n : Nat → UInt256) (inv : UInt256) (rest : List UInt256)
    (h : SquareMeaning.Memory0 s.memory inv a b n) :
    SquareMeaning.Memory0 (completed s a n rest).memory inv (normalized a n) b n := by
  by_cases hz : (overflowFlag a).toNat = 0
  · simpa only [completed, normalized, if_pos hz] using h
  · simp only [completed, normalized, if_neg hz]
    constructor <;>
      simp (disch := decide) only [NormalizeBinding.returned, result, cells, storeCells, writeCell,
        readStore, Challenge.EvmProof.Memory.readWord_writeWord,
        h.at1344, h.at1376, h.at2720, h.at1568, h.at1600]

theorem frame_output (s : State) (a n : Nat → UInt256) (rest : List UInt256) :
    (completed s a n rest).stack = frame (normalized a n) n (n 0) (n 1) rest := by
  by_cases hz : (overflowFlag a).toNat = 0
  · simp only [completed, normalized, if_pos hz]
  · simp only [completed, normalized, if_neg hz, NormalizeBinding.returned]

end CycleSubmission.SquareNormalize
