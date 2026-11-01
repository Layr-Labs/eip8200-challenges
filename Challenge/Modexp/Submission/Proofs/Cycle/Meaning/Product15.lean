import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product15
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

attribute [local irreducible] productC0 productQ0 productC1 productQ1 productC2 productQ2 productC3 productQ3 productC4 productQ4 productC5 productQ5 productC6 productQ6 productC7 productQ7 productC8 productQ8 productC9 productD0 productC10 productC11 productD1

def cells15 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(832, (productD2 inv a b n))]

def result15 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 9796
    memory := storeCells s.memory (cells15 inv a b n)
    stack := frame16 inv a b n rest}

theorem model15_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory15 s.memory inv a b n) :
    productColumn15Model s ((productQ7 inv a b n)) ((((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n)))))))))))) (((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n)))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = result15 s inv a b n rest := by
  simp (disch := decide) only [productColumn15Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800]
  dsimp only [result15, cells15, frame16, productC12, productD2, CycleSubmission.DirectRecovery.carry, storeCells, writeCell]
  simp only [HistoricalSearch.WordCancellation.land_comm]
  rfl

theorem run15 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory15 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn15Program
      {s with pc := UInt256.ofNat 9668, stack := frame15 inv a b n rest} =
      some (result15 s inv a b n rest) := by
  have hx := productColumn15_run s ((productQ7 inv a b n)) ((((n 5) * (productQ6 inv a b n)) + (((n 6) * (productQ5 inv a b n)) + (((n 7) * (productQ4 inv a b n)) + (((n 8) * (productQ3 inv a b n)) + (((b 3) * (a 8)) + (((b 4) * (a 7)) + (((b 5) * (a 6)) + (((b 6) * (a 5)) + (((b 7) * (a 4)) + (((b 8) * (a 3)) + (productC11 inv a b n)))))))))))) (((UInt256.mulMod (b 3) (a 8) P) + ((UInt256.mulMod (b 4) (a 7) P) + ((UInt256.mulMod (b 5) (a 6) P) + ((UInt256.mulMod (b 6) (a 5) P) + ((UInt256.mulMod (b 7) (a 4) P) + ((UInt256.mulMod (b 8) (a 3) P) + (productC11 inv a b n)))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest hcap hact
  rw [model15_eq s inv a b n rest h] at hx
  exact hx

theorem memory15_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory15 s.memory inv a b n) :
    Memory16 (result15 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result15, cells15, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280, h.at800]

end CycleSubmission.ProductMeaning
