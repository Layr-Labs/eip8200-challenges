import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square11
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

def cells11 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(832, (squareD2 inv a b n))]

def result11 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7693
    memory := storeCells s.memory (cells11 inv a b n)
    stack := frame12 inv a b n rest}

theorem model11_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory11 s.memory inv a b n) :
    squareColumn11Model s ((a 5)) ((a 6)) (P) (((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P))) (((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))))) ((squareC11 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest = result11 s inv a b n rest := by
  simp (disch := decide) only [squareColumn11Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800]
  rfl

theorem run11 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory11 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn11Program
      {s with pc := UInt256.ofNat 7563, stack := frame11 inv a b n rest} =
      some (result11 s inv a b n rest) := by
  have hx := squareColumn11_run s ((a 5)) ((a 6)) (P) (((UInt256.mulMod (a 4) (a 7) P) + (UInt256.mulMod (a 8) (a 3) P))) (((((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))) + (((a 5) * (a 6)) + (((a 4) * (a 7)) + ((a 8) * (a 3)))))) ((squareC11 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest hcap hact
  rw [model11_eq s inv a b n rest h] at hx
  exact hx

theorem memory11_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory11 s.memory inv a b n) :
    Memory12 (result11 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result11, cells11, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800]

end CycleSubmission.SquareMeaning
