import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square5
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

def cells5 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(1088, (squareQ1 inv a b n))]

def result5 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6463
    memory := storeCells s.memory (cells5 inv a b n)
    stack := frame6 inv a b n rest}

theorem model5_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory5 s.memory inv a b n) :
    squareColumn5Model s ((a 2)) ((a 5)) ((((a 6) * (a 1)) + ((a 7) * (a 0)))) ((a 0)) (P) ((a 7)) ((squareQ1 inv a b n)) ((squareC7 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result5 s inv a b n rest := by
  simp (disch := decide) only [squareColumn5Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248]
  rfl

theorem run5 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory5 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn5Program
      {s with pc := UInt256.ofNat 6335, stack := frame5 inv a b n rest} =
      some (result5 s inv a b n rest) := by
  have hx := squareColumn5_run s ((a 2)) ((a 5)) ((((a 6) * (a 1)) + ((a 7) * (a 0)))) ((a 0)) (P) ((a 7)) ((squareQ1 inv a b n)) ((squareC7 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model5_eq s inv a b n rest h] at hx
  exact hx

theorem memory5_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory5 s.memory inv a b n) :
    Memory6 (result5 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result5, cells5, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248]

end CycleSubmission.SquareMeaning
