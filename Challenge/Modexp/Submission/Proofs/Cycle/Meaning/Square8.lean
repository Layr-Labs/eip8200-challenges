import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square8
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

def cells8 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  []

def result8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7306
    memory := storeCells s.memory (cells8 inv a b n)
    stack := frame9 inv a b n rest}

theorem model8_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory8 s.memory inv a b n) :
    squareColumn8Model s ((a 6)) ((((a 2) * (a 7)) + ((a 8) * (a 1)))) ((a 1)) (P) ((a 8)) ((squareC9 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest = result8 s inv a b n rest := by
  simp (disch := decide) only [squareColumn8Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory8 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn8Program
      {s with pc := UInt256.ofNat 7177, stack := frame8 inv a b n rest} =
      some (result8 s inv a b n rest) := by
  have hx := squareColumn8_run s ((a 6)) ((((a 2) * (a 7)) + ((a 8) * (a 1)))) ((a 1)) (P) ((a 8)) ((squareC9 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest hcap hact
  rw [model8_eq s inv a b n rest h] at hx
  exact hx

theorem memory8_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory8 s.memory inv a b n) :
    Memory9 (result8 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result8, cells8, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.SquareMeaning
