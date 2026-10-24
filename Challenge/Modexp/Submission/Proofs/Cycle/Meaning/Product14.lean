import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product14
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

def cells14 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(800, (productD1 inv a b n))]

def result14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 10126
    memory := storeCells s.memory (cells14 inv a b n)
    stack := frame15 inv a b n rest}

theorem model14_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory14 s.memory inv a b n) :
    productColumn14Model s ((UInt256.ofNat 16)) ((UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (productQ8 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ7 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ2 inv a b n) P) + ((UInt256.mulMod (b 2) (a 8) P) + ((UInt256.mulMod (b 3) (a 7) P) + ((UInt256.mulMod (b 4) (a 6) P) + ((UInt256.mulMod (b 5) (a 5) P) + ((UInt256.mulMod (b 6) (a 4) P) + ((UInt256.mulMod (b 7) (a 3) P) + ((UInt256.mulMod (a 2) (b 8) P) + (productC10 inv a b n))))))))))))))) (UInt256.lnot (((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n)))))))))))))))) P) (UInt256.ofNat 5))) ((((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n)))))))))))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest = result14 s inv a b n rest := by
  simp (disch := decide) only [productColumn14Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run14 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory14 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn14Program
      {s with pc := UInt256.ofNat 9998, stack := frame14 inv a b n rest} =
      some (result14 s inv a b n rest) := by
  have hx := productColumn14_run s ((UInt256.ofNat 16)) ((UInt256.shiftRight (UInt256.addMod ((UInt256.mulMod (productQ8 inv a b n) (n 2) P) + ((UInt256.mulMod (productQ7 inv a b n) (n 3) P) + ((UInt256.mulMod (n 4) (productQ6 inv a b n) P) + ((UInt256.mulMod (n 5) (productQ5 inv a b n) P) + ((UInt256.mulMod (n 6) (productQ4 inv a b n) P) + ((UInt256.mulMod (n 7) (productQ3 inv a b n) P) + ((UInt256.mulMod (n 8) (productQ2 inv a b n) P) + ((UInt256.mulMod (b 2) (a 8) P) + ((UInt256.mulMod (b 3) (a 7) P) + ((UInt256.mulMod (b 4) (a 6) P) + ((UInt256.mulMod (b 5) (a 5) P) + ((UInt256.mulMod (b 6) (a 4) P) + ((UInt256.mulMod (b 7) (a 3) P) + ((UInt256.mulMod (a 2) (b 8) P) + (productC10 inv a b n))))))))))))))) (UInt256.lnot (((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n)))))))))))))))) P) (UInt256.ofNat 5))) ((((productQ8 inv a b n) * (n 2)) + (((n 3) * (productQ7 inv a b n)) + (((n 4) * (productQ6 inv a b n)) + (((n 5) * (productQ5 inv a b n)) + (((n 6) * (productQ4 inv a b n)) + (((n 7) * (productQ3 inv a b n)) + (((n 8) * (productQ2 inv a b n)) + (((b 2) * (a 8)) + (((b 3) * (a 7)) + (((b 4) * (a 6)) + (((b 5) * (a 5)) + (((b 6) * (a 4)) + (((b 7) * (a 3)) + (((a 2) * (b 8)) + (productC10 inv a b n)))))))))))))))) ((a 8)) ((n 6)) ((n 4)) ((productQ6 inv a b n)) ((productQ5 inv a b n)) ((n 5)) ((n 7)) (P) ((n 8)) ((productQ7 inv a b n)) ((UInt256.ofNat (2^240-1))) ((productQ8 inv a b n)) ((n 3)) ((n 2)) rest hcap hact
  rw [model14_eq s inv a b n rest h] at hx
  exact hx

theorem memory14_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory14 s.memory inv a b n) :
    Memory15 (result14 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result14, cells14, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.ProductMeaning
