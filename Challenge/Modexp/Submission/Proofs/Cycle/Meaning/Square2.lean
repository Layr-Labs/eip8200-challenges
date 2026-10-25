import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square2
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

def cells2 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(224, (squareQ4 inv a b n))]

def result2 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6079
    memory := storeCells s.memory (cells2 inv a b n)
    stack := frame3 inv a b n rest}

theorem model2_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory2 s.memory inv a b n) :
    squareColumn2Model s ((UInt256.mulMod (a 1) (a 3) P)) ((UInt256.mulMod (a 4) (a 0) P)) (((((a 1) * (a 3)) + ((a 4) * (a 0))) + (((a 1) * (a 3)) + ((a 4) * (a 0))))) ((squareC4 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result2 s inv a b n rest := by
  simp (disch := decide) only [squareColumn2Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0]
  rfl

theorem run2 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory2 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn2Program
      {s with pc := UInt256.ofNat 5951, stack := frame2 inv a b n rest} =
      some (result2 s inv a b n rest) := by
  have hx := squareColumn2_run s ((UInt256.mulMod (a 1) (a 3) P)) ((UInt256.mulMod (a 4) (a 0) P)) (((((a 1) * (a 3)) + ((a 4) * (a 0))) + (((a 1) * (a 3)) + ((a 4) * (a 0))))) ((squareC4 inv a b n)) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model2_eq s inv a b n rest h] at hx
  exact hx

theorem memory2_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory2 s.memory inv a b n) :
    Memory3 (result2 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result2, cells2, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0]

end CycleSubmission.SquareMeaning
