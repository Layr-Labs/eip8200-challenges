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
  {s with pc := UInt256.ofNat 7619, stack := frame a n (n 0) (n 1) rest}
def completed (s : State) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  if (overflowFlag a).toNat = 0 then
    {s with pc := UInt256.ofNat 7619, stack := frame a n (n 0) (n 1) rest}
  else NormalizeBinding.returned s a n (UInt256.ofNat 7619) (n 1) rest

/-- There is no overflow test any more: the square loop keeps its operands below `R - 2N`, so the
kernel's top digit never reaches `2^240` and the normalization branch is not needed. -/
noncomputable def gasSteps (s : State) (a n : Nat → UInt256) (rest : List UInt256)
    (hz : (overflowFlag a).toNat = 0) :
    GasSteps (initial s a n rest) (completed s a n rest) := by
  have he : completed s a n rest = initial s a n rest := by
    simp only [completed, initial, if_pos hz]
  rw [he]
  exact GasSteps.refl _

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
