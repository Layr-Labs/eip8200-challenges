import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square14
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

def cells14 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(128, (squareD6 inv a b n)), (160, (squareD7 inv a b n))]

def result14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7619
    memory := storeCells s.memory (cells14 inv a b n)
    stack := frame15 inv a b n rest}

theorem model14_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory14 s.memory inv a b n) :
    squareColumn14Model s ((squareC15 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest = result14 s inv a b n rest := by
  simp (disch := decide) only [squareColumn14Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800, h.at832]
  rfl

theorem run14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory14 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn14Program
      {s with pc := UInt256.ofNat 7498, stack := frame14 inv a b n rest} =
      some (result14 s inv a b n rest) := by
  have hx := squareColumn14_run s ((squareC15 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest hcap hact
  rw [model14_eq s inv a b n rest h] at hx
  exact hx

theorem memory14_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory14 s.memory inv a b n) :
    Memory15 (result14 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result14, cells14, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800, h.at832]

end CycleSubmission.SquareMeaning
