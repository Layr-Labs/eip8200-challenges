import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square1
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

def cells1 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(192, (squareQ2 inv a b n)), (0, (squareQ3 inv a b n))]

def result1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6409
    memory := storeCells s.memory (cells1 inv a b n)
    stack := frame2 inv a b n rest}

theorem model1_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory1 s.memory inv a b n) :
    squareColumn1Model s ((n 0)) (P) (((UInt256.mulMod (squareQ1 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 2) P) + ((UInt256.mulMod (a 1) (a 1) P) + ((squareC2 inv a b n) + ((UInt256.mulMod (a 2) (a 0) P) + (UInt256.mulMod (a 2) (a 0) P))))))) ((((squareQ1 inv a b n) * (n 1)) + (((squareQ0 inv a b n) * (n 2)) + (((a 1) * (a 1)) + ((squareC2 inv a b n) + (((a 2) * (a 0)) + ((a 2) * (a 0)))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result1 s inv a b n rest := by
  simp (disch := decide) only [squareColumn1Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160]
  rfl

theorem run1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory1 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn1Program
      {s with pc := UInt256.ofNat 6281, stack := frame1 inv a b n rest} =
      some (result1 s inv a b n rest) := by
  have hx := squareColumn1_run s ((n 0)) (P) (((UInt256.mulMod (squareQ1 inv a b n) (n 1) P) + ((UInt256.mulMod (squareQ0 inv a b n) (n 2) P) + ((UInt256.mulMod (a 1) (a 1) P) + ((squareC2 inv a b n) + ((UInt256.mulMod (a 2) (a 0) P) + (UInt256.mulMod (a 2) (a 0) P))))))) ((((squareQ1 inv a b n) * (n 1)) + (((squareQ0 inv a b n) * (n 2)) + (((a 1) * (a 1)) + ((squareC2 inv a b n) + (((a 2) * (a 0)) + ((a 2) * (a 0)))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model1_eq s inv a b n rest h] at hx
  exact hx

theorem memory1_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory1 s.memory inv a b n) :
    Memory2 (result1 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result1, cells1, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160]

end CycleSubmission.SquareMeaning
