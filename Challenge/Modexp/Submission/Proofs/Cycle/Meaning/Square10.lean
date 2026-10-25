import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square10
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

def cells10 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(800, (squareD1 inv a b n))]

def result10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7105
    memory := storeCells s.memory (cells10 inv a b n)
    stack := frame11 inv a b n rest}

theorem model10_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory10 s.memory inv a b n) :
    squareColumn10Model s ((squareQ5 inv a b n)) ((n 5)) ((((squareQ4 inv a b n) * (n 6)) + (((n 7) * (squareQ3 inv a b n)) + (((n 8) * (squareQ2 inv a b n)) + (((a 5) * (a 5)) + ((squareC10 inv a b n) + ((((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))) + (((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2))))))))))) (((squareC10 inv a b n) + (((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P))) + ((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P)))))) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest = result10 s inv a b n rest := by
  simp (disch := decide) only [squareColumn10Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory10 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn10Program
      {s with pc := UInt256.ofNat 6976, stack := frame10 inv a b n rest} =
      some (result10 s inv a b n rest) := by
  have hx := squareColumn10_run s ((squareQ5 inv a b n)) ((n 5)) ((((squareQ4 inv a b n) * (n 6)) + (((n 7) * (squareQ3 inv a b n)) + (((n 8) * (squareQ2 inv a b n)) + (((a 5) * (a 5)) + ((squareC10 inv a b n) + ((((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2)))) + (((a 4) * (a 6)) + (((a 3) * (a 7)) + ((a 8) * (a 2))))))))))) (((squareC10 inv a b n) + (((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P))) + ((UInt256.mulMod (a 4) (a 6) P) + ((UInt256.mulMod (a 3) (a 7) P) + (UInt256.mulMod (a 8) (a 2) P)))))) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((squareQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((squareQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest hcap hact
  rw [model10_eq s inv a b n rest h] at hx
  exact hx

theorem memory10_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory10 s.memory inv a b n) :
    Memory11 (result10 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result10, cells10, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.SquareMeaning
