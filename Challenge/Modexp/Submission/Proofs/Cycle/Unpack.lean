import Challenge.Modexp.Submission.Proofs.Cycle.Execution.UnpackFinal
import Challenge.Modexp.Submission.Proofs.Cycle.InputWords
import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.Unpack
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.InputWords CycleSubmission.Execution CycleSubmission.WordArithmetic
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning (readStore)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

def cells (b : Nat → UInt256) : List (Nat × UInt256) :=
  [(1792,b 0),(1824,b 1),(1856,b 2),(1888,b 3),(1920,b 4),
   (1952,b 5),(1984,b 6),(2016,b 7),(2048,b 8)]

def result (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 7744
    memory := storeCells s.memory (cells (ordinary s.memory 256))
    stack := ProductMeaning.frame0 inv a (ordinary s.memory 256) n rest}

theorem model_eq (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256) :
    unpackFinalModel s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7)
      P (n 8) (n 1) (UInt256.ofNat (2^240-1)) (n 0) (n 3) (a 8) rest =
      result s inv a n rest := by
  simp (disch := decide) only [unpackFinalModel, readStore]
  rfl

theorem run (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 960) (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions unpackFinalProgram
      {s with pc := UInt256.ofNat 7652, stack := SquareMeaning.frame0 inv a (fun _ => UInt256.ofNat 0) n rest} =
      some (result s inv a n rest) := by
  have h := unpackFinal_run s (n 2) (n 6) (n 4) (a 1) (a 2) (n 5) (n 7)
    P (n 8) (n 1) (UInt256.ofNat (2^240-1)) (n 0) (n 3) (a 8) rest hcap hact
  rw [model_eq s inv a n rest] at h
  exact h

theorem memory_output (s : State) (inv : UInt256) (a n : Nat → UInt256) (rest : List UInt256)
    (h : SquareMeaning.Memory0 s.memory inv a (fun _ => UInt256.ofNat 0) n) :
    ProductMeaning.Memory0 (result s inv a n rest).memory inv a (ordinary s.memory 256) n := by
  constructor <;>
    simp (disch := decide) only [result, cells, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720,
      h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160]

end CycleSubmission.Unpack
