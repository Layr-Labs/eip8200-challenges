import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square13
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

def cells13 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(64, (squareD4 inv a b n)), (96, (squareD5 inv a b n))]

def result13 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7950
    memory := storeCells s.memory (cells13 inv a b n)
    stack := frame14 inv a b n rest}

theorem model13_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory13 s.memory inv a b n) :
    squareColumn13Model s (((n 6) * (squareQ7 inv a b n))) ((((n 7) * (squareQ6 inv a b n)) + (((n 8) * (squareQ5 inv a b n)) + ((squareC13 inv a b n) + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5)))))))) (((squareC13 inv a b n) + (((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)) + ((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P))))) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest = result13 s inv a b n rest := by
  simp (disch := decide) only [squareColumn13Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800, h.at832]
  rfl

theorem run13 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory13 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn13Program
      {s with pc := UInt256.ofNat 7821, stack := frame13 inv a b n rest} =
      some (result13 s inv a b n rest) := by
  have hx := squareColumn13_run s (((n 6) * (squareQ7 inv a b n))) ((((n 7) * (squareQ6 inv a b n)) + (((n 8) * (squareQ5 inv a b n)) + ((squareC13 inv a b n) + ((((a 6) * (a 7)) + ((a 8) * (a 5))) + (((a 6) * (a 7)) + ((a 8) * (a 5)))))))) (((squareC13 inv a b n) + (((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P)) + ((UInt256.mulMod (a 6) (a 7) P) + (UInt256.mulMod (a 8) (a 5) P))))) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest hcap hact
  rw [model13_eq s inv a b n rest h] at hx
  exact hx

theorem memory13_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory13 s.memory inv a b n) :
    Memory14 (result13 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result13, cells13, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800, h.at832]

end CycleSubmission.SquareMeaning
