import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Square3
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

def cells3 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(1216, (squareQ5 inv a b n))]

def result3 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 6665
    memory := storeCells s.memory (cells3 inv a b n)
    stack := frame4 inv a b n rest}

theorem model3_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory3 s.memory inv a b n) :
    squareColumn3Model s ((n 5)) (((squareC5 inv a b n) + ((((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0)))) + (((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0))))))) (((squareC5 inv a b n) + (((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P))) + ((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P)))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result3 s inv a b n rest := by
  simp (disch := decide) only [squareColumn3Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224]
  rfl

theorem run3 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory3 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions squareColumn3Program
      {s with pc := UInt256.ofNat 6537, stack := frame3 inv a b n rest} =
      some (result3 s inv a b n rest) := by
  have hx := squareColumn3_run s ((n 5)) (((squareC5 inv a b n) + ((((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0)))) + (((a 2) * (a 3)) + (((a 1) * (a 4)) + ((a 5) * (a 0))))))) (((squareC5 inv a b n) + (((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P))) + ((UInt256.mulMod (a 2) (a 3) P) + ((UInt256.mulMod (a 1) (a 4) P) + (UInt256.mulMod (a 5) (a 0) P)))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((squareQ1 inv a b n)) (P) ((squareQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model3_eq s inv a b n rest h] at hx
  exact hx

theorem memory3_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory3 s.memory inv a b n) :
    Memory4 (result3 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result3, cells3, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at192, h.at0, h.at224]

end CycleSubmission.SquareMeaning
