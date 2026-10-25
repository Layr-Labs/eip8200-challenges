import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product1
import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace CycleSubmission.ProductMeaning
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.WordArithmetic CycleSubmission.WordHistory
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning (readStore)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open CycleSubmission.Execution

def cells1 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(192, (productQ2 inv a b n))]

def result1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 8002
    memory := storeCells s.memory (cells1 inv a b n)
    stack := frame2 inv a b n rest}

theorem model1_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory1 s.memory inv a b n) :
    productColumn1Model s (((UInt256.mulMod (b 1) (a 1) P) + ((UInt256.mulMod (b 2) (a 0) P) + (productC2 inv a b n)))) ((((b 1) * (a 1)) + (((b 2) * (a 0)) + (productC2 inv a b n)))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result1 s inv a b n rest := by
  simp (disch := decide) only [productColumn1Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048]
  rfl

theorem run1 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory1 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn1Program
      {s with pc := UInt256.ofNat 7872, stack := frame1 inv a b n rest} =
      some (result1 s inv a b n rest) := by
  have hx := productColumn1_run s (((UInt256.mulMod (b 1) (a 1) P) + ((UInt256.mulMod (b 2) (a 0) P) + (productC2 inv a b n)))) ((((b 1) * (a 1)) + (((b 2) * (a 0)) + (productC2 inv a b n)))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model1_eq s inv a b n rest h] at hx
  exact hx

theorem memory1_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory1 s.memory inv a b n) :
    Memory2 (result1 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result1, cells1, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048]

end CycleSubmission.ProductMeaning
