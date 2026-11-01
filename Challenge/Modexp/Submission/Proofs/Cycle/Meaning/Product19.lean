import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product19
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

attribute [local irreducible] productC0 productQ0 productC1 productQ1 productC2 productQ2 productC3 productQ3 productC4 productQ4 productC5 productQ5 productC6 productQ6 productC7 productQ7 productC8 productQ8 productC9 productD0 productC10 productC11 productD1 productC12 productD2 productC13 productD3 productD4 productC14 productD5 productC15 productD6 productC16

def cells19 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(160, (productD7 inv a b n))]

def result19 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10234
    memory := storeCells s.memory (cells19 inv a b n)
    stack := frame20 inv a b n rest}

theorem model19_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory19 s.memory inv a b n) :
    productColumn19Model s ((productC16 inv a b n)) ((b 8)) ((a 8)) ((n 6)) ((n 4)) ((productD1 inv a b n)) ((productD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = result19 s inv a b n rest := by
  simp (disch := decide) only [productColumn19Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800, h.at832]
  dsimp only [result19, cells19, frame20, productC17, productD7, CycleSubmission.DirectRecovery.carry, storeCells, writeCell]
  simp only [HistoricalSearch.WordCancellation.land_comm]
  rfl

theorem run19 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory19 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn19Program
      {s with pc := UInt256.ofNat 10190, stack := frame19 inv a b n rest} =
      some (result19 s inv a b n rest) := by
  have hx := productColumn19_run s ((productC16 inv a b n)) ((b 8)) ((a 8)) ((n 6)) ((n 4)) ((productD1 inv a b n)) ((productD2 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest hcap hact
  rw [model19_eq s inv a b n rest h] at hx
  exact hx

theorem memory19_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory19 s.memory inv a b n) :
    Memory20 (result19 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result19, cells19, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800, h.at832]

end CycleSubmission.ProductMeaning
