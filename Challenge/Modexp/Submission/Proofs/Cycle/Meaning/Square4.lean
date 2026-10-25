import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square4
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

def cells4 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(1248, (squareQ6 inv a b n))]

def result4 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6335
    memory := storeCells s.memory (cells4 inv a b n)
    stack := frame5 inv a b n rest}

theorem model4_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory4 s.memory inv a b n) :
    squareColumn4Model s ((a 3)) ((a 3)) (((squareC6 inv a b n) + ((((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0)))) + (((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0))))))) (((squareC6 inv a b n) + (((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P))) + ((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P)))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result4 s inv a b n rest := by
  simp (disch := decide) only [squareColumn4Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216]
  rfl

theorem run4 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory4 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn4Program
      {s with pc := UInt256.ofNat 6207, stack := frame4 inv a b n rest} =
      some (result4 s inv a b n rest) := by
  have hx := squareColumn4_run s ((a 3)) ((a 3)) (((squareC6 inv a b n) + ((((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0)))) + (((a 2) * (a 4)) + (((a 1) * (a 5)) + ((a 6) * (a 0))))))) (((squareC6 inv a b n) + (((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P))) + ((UInt256.mulMod (a 2) (a 4) P) + ((UInt256.mulMod (a 1) (a 5) P) + (UInt256.mulMod (a 6) (a 0) P)))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model4_eq s inv a b n rest h] at hx
  exact hx

theorem memory4_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory4 s.memory inv a b n) :
    Memory5 (result4 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result4, cells4, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216]

end CycleSubmission.SquareMeaning
