import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square0
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.SquareMeaning
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning (readStore)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open CycleSubmission.Execution

def cells0 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  []

def result0 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6281
    memory := storeCells s.memory (cells0 inv a b n)
    stack := frame1 inv a b n rest}

theorem model0_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) :
    squareColumn0Model s ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result0 s inv a b n rest := by
  simp (disch := decide) only [squareColumn0Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160]
  rfl

theorem run0 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn0Program
      {s with pc := UInt256.ofNat 6153, stack := frame0 inv a b n rest} =
      some (result0 s inv a b n rest) := by
  have hx := squareColumn0_run s ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model0_eq s inv a b n rest h] at hx
  exact hx

theorem memory0_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory0 s.memory inv a b n) :
    Memory1 (result0 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result0, cells0, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160]

end CycleSubmission.SquareMeaning
