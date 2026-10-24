import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square9
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

def cells9 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(768, (squareD0 inv a b n))]

def result9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7434
    memory := storeCells s.memory (cells9 inv a b n)
    stack := frame10 inv a b n rest}

theorem model9_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory9 s.memory inv a b n) :
    squareColumn9Model s ((squareQ5 inv a b n)) ((n 4)) (P) (((UInt256.mulMod (squareQ4 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ2 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ1 inv a b n) P) + ((squareC9 inv a b n) + (((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))) + ((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P))))))))))) ((((squareQ8 inv a b n) * (n 1)) + (((squareQ7 inv a b n) * (n 2)) + (((squareQ6 inv a b n) * (n 3)) + (((squareQ5 inv a b n) * (n 4)) + (((squareQ4 inv a b n) * (n 5)) + (((squareQ3 inv a b n) * (n 6)) + (((n 7) * (squareQ2 inv a b n)) + (((n 8) * (squareQ1 inv a b n)) + ((squareC9 inv a b n) + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1)))))))))))))))) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest = result9 s inv a b n rest := by
  simp (disch := decide) only [squareColumn9Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory9 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn9Program
      {s with pc := UInt256.ofNat 7306, stack := frame9 inv a b n rest} =
      some (result9 s inv a b n rest) := by
  have hx := squareColumn9_run s ((squareQ5 inv a b n)) ((n 4)) (P) (((UInt256.mulMod (squareQ4 inv a b n) (n 5) P) + ((UInt256.mulMod (squareQ3 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (squareQ2 inv a b n) P) + ((UInt256.mulMod (n 8) (squareQ1 inv a b n) P) + ((squareC9 inv a b n) + (((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P)))) + ((UInt256.mulMod (a 4) (a 5) P) + ((UInt256.mulMod (a 3) (a 6) P) + ((UInt256.mulMod (a 2) (a 7) P) + (UInt256.mulMod (a 8) (a 1) P))))))))))) ((((squareQ8 inv a b n) * (n 1)) + (((squareQ7 inv a b n) * (n 2)) + (((squareQ6 inv a b n) * (n 3)) + (((squareQ5 inv a b n) * (n 4)) + (((squareQ4 inv a b n) * (n 5)) + (((squareQ3 inv a b n) * (n 6)) + (((n 7) * (squareQ2 inv a b n)) + (((n 8) * (squareQ1 inv a b n)) + ((squareC9 inv a b n) + ((((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1))))) + (((a 4) * (a 5)) + (((a 3) * (a 6)) + (((a 2) * (a 7)) + ((a 8) * (a 1)))))))))))))))) ((n 2)) ((n 6)) ((n 4)) ((squareQ6 inv a b n)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((squareQ8 inv a b n)) ((n 3)) ((a 8)) rest hcap hact
  rw [model9_eq s inv a b n rest h] at hx
  exact hx

theorem memory9_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory9 s.memory inv a b n) :
    Memory10 (result9 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result9, cells9, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.SquareMeaning
