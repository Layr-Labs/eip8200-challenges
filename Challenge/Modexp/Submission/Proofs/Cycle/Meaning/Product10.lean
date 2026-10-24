import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product10
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

def cells10 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  []

def result10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 9614
    memory := storeCells s.memory (cells10 inv a b n)
    stack := frame11 inv a b n rest}

theorem model10_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory10 s.memory inv a b n) :
    productColumn10Model s ((UInt256.mulMod (n 6) (productQ2 inv a b n) P)) (((UInt256.mulMod (n 7) (productQ1 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 8) P) + ((UInt256.mulMod (b 1) (a 7) P) + ((UInt256.mulMod (b 2) (a 6) P) + ((UInt256.mulMod (b 3) (a 5) P) + ((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n))))))))))))) ((((n 1) * (productQ7 inv a b n)) + (((productQ6 inv a b n) * (n 2)) + (((n 3) * (productQ5 inv a b n)) + (((n 4) * (productQ4 inv a b n)) + (((n 5) * (productQ3 inv a b n)) + (((n 6) * (productQ2 inv a b n)) + (((n 7) * (productQ1 inv a b n)) + (((n 8) * (productQ0 inv a b n)) + (((b 0) * (a 8)) + (((b 1) * (a 7)) + (((b 2) * (a 6)) + (((b 3) * (a 5)) + (((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n))))))))))))))))))) ((a 8)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((n 2)) rest = result10 s inv a b n rest := by
  simp (disch := decide) only [productColumn10Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run10 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory10 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn10Program
      {s with pc := UInt256.ofNat 9484, stack := frame10 inv a b n rest} =
      some (result10 s inv a b n rest) := by
  have hx := productColumn10_run s ((UInt256.mulMod (n 6) (productQ2 inv a b n) P)) (((UInt256.mulMod (n 7) (productQ1 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 8) P) + ((UInt256.mulMod (b 1) (a 7) P) + ((UInt256.mulMod (b 2) (a 6) P) + ((UInt256.mulMod (b 3) (a 5) P) + ((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n))))))))))))) ((((n 1) * (productQ7 inv a b n)) + (((productQ6 inv a b n) * (n 2)) + (((n 3) * (productQ5 inv a b n)) + (((n 4) * (productQ4 inv a b n)) + (((n 5) * (productQ3 inv a b n)) + (((n 6) * (productQ2 inv a b n)) + (((n 7) * (productQ1 inv a b n)) + (((n 8) * (productQ0 inv a b n)) + (((b 0) * (a 8)) + (((b 1) * (a 7)) + (((b 2) * (a 6)) + (((b 3) * (a 5)) + (((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n))))))))))))))))))) ((a 8)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((n 8)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((n 2)) rest hcap hact
  rw [model10_eq s inv a b n rest h] at hx
  exact hx

theorem memory10_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory10 s.memory inv a b n) :
    Memory11 (result10 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result10, cells10, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.ProductMeaning
