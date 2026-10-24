import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product8
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

def cells8 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  [(1280, (productQ7 inv a b n))]

def result8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 9356
    memory := storeCells s.memory (cells8 inv a b n)
    stack := frame9 inv a b n rest}

theorem model8_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory8 s.memory inv a b n) :
    productColumn8Model s (P) (((UInt256.mulMod (productQ4 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 4) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 7) P) + ((UInt256.mulMod (b 1) (a 6) P) + ((UInt256.mulMod (b 2) (a 5) P) + ((UInt256.mulMod (b 3) (a 4) P) + ((UInt256.mulMod (b 4) (a 3) P) + ((UInt256.mulMod (b 5) (a 2) P) + ((UInt256.mulMod (b 6) (a 1) P) + ((UInt256.mulMod (b 7) (a 0) P) + (productC7 inv a b n))))))))))))))) ((((productQ6 inv a b n) * (n 1)) + (((productQ5 inv a b n) * (n 2)) + (((productQ4 inv a b n) * (n 3)) + (((productQ3 inv a b n) * (n 4)) + (((productQ2 inv a b n) * (n 5)) + (((productQ1 inv a b n) * (n 6)) + (((n 7) * (productQ0 inv a b n)) + (((b 0) * (a 7)) + (((b 1) * (a 6)) + (((b 2) * (a 5)) + (((b 3) * (a 4)) + (((b 4) * (a 3)) + (((b 5) * (a 2)) + (((b 6) * (a 1)) + (((b 7) * (a 0)) + (productC7 inv a b n))))))))))))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest = result8 s inv a b n rest := by
  simp (disch := decide) only [productColumn8Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088]
  rfl

theorem run8 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory8 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn8Program
      {s with pc := UInt256.ofNat 9228, stack := frame8 inv a b n rest} =
      some (result8 s inv a b n rest) := by
  have hx := productColumn8_run s (P) (((UInt256.mulMod (productQ4 inv a b n) (n 3) P) + ((UInt256.mulMod (productQ3 inv a b n) (n 4) P) + ((UInt256.mulMod (productQ2 inv a b n) (n 5) P) + ((UInt256.mulMod (productQ1 inv a b n) (n 6) P) + ((UInt256.mulMod (n 7) (productQ0 inv a b n) P) + ((UInt256.mulMod (b 0) (a 7) P) + ((UInt256.mulMod (b 1) (a 6) P) + ((UInt256.mulMod (b 2) (a 5) P) + ((UInt256.mulMod (b 3) (a 4) P) + ((UInt256.mulMod (b 4) (a 3) P) + ((UInt256.mulMod (b 5) (a 2) P) + ((UInt256.mulMod (b 6) (a 1) P) + ((UInt256.mulMod (b 7) (a 0) P) + (productC7 inv a b n))))))))))))))) ((((productQ6 inv a b n) * (n 1)) + (((productQ5 inv a b n) * (n 2)) + (((productQ4 inv a b n) * (n 3)) + (((productQ3 inv a b n) * (n 4)) + (((productQ2 inv a b n) * (n 5)) + (((productQ1 inv a b n) * (n 6)) + (((n 7) * (productQ0 inv a b n)) + (((b 0) * (a 7)) + (((b 1) * (a 6)) + (((b 2) * (a 5)) + (((b 3) * (a 4)) + (((b 4) * (a 3)) + (((b 5) * (a 2)) + (((b 6) * (a 1)) + (((b 7) * (a 0)) + (productC7 inv a b n))))))))))))))))) ((n 2)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((a 8)) rest hcap hact
  rw [model8_eq s inv a b n rest h] at hx
  exact hx

theorem memory8_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory8 s.memory inv a b n) :
    Memory9 (result8 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result8, cells8, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088]

end CycleSubmission.ProductMeaning
