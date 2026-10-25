import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square7
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

def cells7 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  []

def result7 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6719
    memory := storeCells s.memory (cells7 inv a b n)
    stack := frame8 inv a b n rest}

theorem model7_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory7 s.memory inv a b n) :
    squareColumn7Model s (((squareQ3 inv a b n) * (n 5))) ((((squareQ2 inv a b n) * (n 6)) + (((n 7) * (squareQ1 inv a b n)) + (((n 8) * (squareQ0 inv a b n)) + (((a 4) * (a 4)) + ((squareC8 inv a b n) + ((((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))) + (((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0)))))))))))) (((UInt256.mulMod (n 8) (squareQ0 inv a b n) P) + ((squareC8 inv a b n) + (((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result7 s inv a b n rest := by
  simp (disch := decide) only [squareColumn7Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run7 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory7 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn7Program
      {s with pc := UInt256.ofNat 6591, stack := frame7 inv a b n rest} =
      some (result7 s inv a b n rest) := by
  have hx := squareColumn7_run s (((squareQ3 inv a b n) * (n 5))) ((((squareQ2 inv a b n) * (n 6)) + (((n 7) * (squareQ1 inv a b n)) + (((n 8) * (squareQ0 inv a b n)) + (((a 4) * (a 4)) + ((squareC8 inv a b n) + ((((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0))))) + (((a 3) * (a 5)) + (((a 2) * (a 6)) + (((a 7) * (a 1)) + ((a 8) * (a 0)))))))))))) (((UInt256.mulMod (n 8) (squareQ0 inv a b n) P) + ((squareC8 inv a b n) + (((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))) + ((UInt256.mulMod (a 3) (a 5) P) + ((UInt256.mulMod (a 2) (a 6) P) + ((UInt256.mulMod (a 1) (a 7) P) + (UInt256.mulMod (a 8) (a 0) P)))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model7_eq s inv a b n rest h] at hx
  exact hx

theorem memory7_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory7 s.memory inv a b n) :
    Memory8 (result7 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result7, cells7, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.SquareMeaning
