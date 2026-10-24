import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product6
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

def cells6 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(1248, (productQ6 inv a b n))]

def result6 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 9100
    memory := storeCells s.memory (cells6 inv a b n)
    stack := frame7 inv a b n rest}

theorem model6_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory6 s.memory inv a b n) :
    productColumn6Model s ((n 4)) (P) (((UInt256.mulMod (productQ1 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 6) P) + ((UInt256.mulMod (b 0) (a 6) P) + ((UInt256.mulMod (b 1) (a 5) P) + ((UInt256.mulMod (b 2) (a 4) P) + ((UInt256.mulMod (b 3) (a 3) P) + ((UInt256.mulMod (b 4) (a 2) P) + ((UInt256.mulMod (b 5) (a 1) P) + ((UInt256.mulMod (b 6) (a 0) P) + (productC6 inv a b n))))))))))) ((((productQ5 inv a b n) * (n 1)) + (((productQ4 inv a b n) * (n 2)) + (((productQ3 inv a b n) * (n 3)) + (((productQ2 inv a b n) * (n 4)) + (((productQ1 inv a b n) * (n 5)) + (((productQ0 inv a b n) * (n 6)) + (((b 0) * (a 6)) + (((b 1) * (a 5)) + (((b 2) * (a 4)) + (((b 3) * (a 3)) + (((b 4) * (a 2)) + (((b 5) * (a 1)) + (((b 6) * (a 0)) + (productC6 inv a b n))))))))))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result6 s inv a b n rest := by
  simp (disch := decide) only [productColumn6Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216]
  rfl

theorem run6 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory6 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn6Program
      {s with pc := UInt256.ofNat 8972, stack := frame6 inv a b n rest} =
      some (result6 s inv a b n rest) := by
  have hx := productColumn6_run s ((n 4)) (P) (((UInt256.mulMod (productQ1 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ0 inv a b n) (n 6) P) + ((UInt256.mulMod (b 0) (a 6) P) + ((UInt256.mulMod (b 1) (a 5) P) + ((UInt256.mulMod (b 2) (a 4) P) + ((UInt256.mulMod (b 3) (a 3) P) + ((UInt256.mulMod (b 4) (a 2) P) + ((UInt256.mulMod (b 5) (a 1) P) + ((UInt256.mulMod (b 6) (a 0) P) + (productC6 inv a b n))))))))))) ((((productQ5 inv a b n) * (n 1)) + (((productQ4 inv a b n) * (n 2)) + (((productQ3 inv a b n) * (n 3)) + (((productQ2 inv a b n) * (n 4)) + (((productQ1 inv a b n) * (n 5)) + (((productQ0 inv a b n) * (n 6)) + (((b 0) * (a 6)) + (((b 1) * (a 5)) + (((b 2) * (a 4)) + (((b 3) * (a 3)) + (((b 4) * (a 2)) + (((b 5) * (a 1)) + (((b 6) * (a 0)) + (productC6 inv a b n))))))))))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((productQ1 inv a b n)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model6_eq s inv a b n rest h] at hx
  exact hx

theorem memory6_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory6 s.memory inv a b n) :
    Memory7 (result6 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result6, cells6, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216]

end CycleSubmission.ProductMeaning
