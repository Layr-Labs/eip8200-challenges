import Challenge.Modexp.Submission.Proofs.Cycle.ProductFrames
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Product9
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

def cells9 (inv : UInt256) (a b n : Nat → UInt256) : List (Nat × UInt256) :=
  []

def result9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 9026
    memory := storeCells s.memory (cells9 inv a b n)
    stack := frame10 inv a b n rest}

theorem model9_eq (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory9 s.memory inv a b n) :
    productColumn9Model s ((a 5)) ((((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n))))))) ((a 5)) (P) (((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n))))))) ((b 3)) ((a 8)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((n 2)) rest = result9 s inv a b n rest := by
  simp (disch := decide) only [productColumn9Model, readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]
  rfl

theorem run9 (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory9 s.memory inv a b n) (hcap : rest.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions productColumn9Program
      {s with pc := UInt256.ofNat 8898, stack := frame9 inv a b n rest} =
      some (result9 s inv a b n rest) := by
  have hx := productColumn9_run s ((a 5)) ((((b 4) * (a 4)) + (((b 5) * (a 3)) + (((b 6) * (a 2)) + (((b 7) * (a 1)) + (((b 8) * (a 0)) + (productC8 inv a b n))))))) ((a 5)) (P) (((UInt256.mulMod (b 4) (a 4) P) + ((UInt256.mulMod (b 5) (a 3) P) + ((UInt256.mulMod (b 6) (a 2) P) + ((UInt256.mulMod (b 7) (a 1) P) + ((UInt256.mulMod (b 8) (a 0) P) + (productC8 inv a b n))))))) ((b 3)) ((a 8)) ((n 6)) ((n 4)) ((a 1)) ((a 2)) ((n 5)) ((n 7)) (P) ((productQ0 inv a b n)) ((n 1)) ((UInt256.ofNat (2^240-1))) ((n 0)) ((n 3)) ((n 2)) rest hcap hact
  rw [model9_eq s inv a b n rest h] at hx
  exact hx

theorem memory9_output (s : State) (inv : UInt256) (a b n : Nat → UInt256) (rest : List UInt256)
    (h : Memory9 s.memory inv a b n) :
    Memory10 (result9 s inv a b n rest).memory inv a b n := by
  constructor <;>
    simp (disch := decide) only [result9, cells9, storeCells, writeCell,
      readStore, readWord_writeWord, h.at768, h.at1344, h.at1376, h.at2720, h.at1568, h.at1600, h.at32, h.at64, h.at96, h.at128, h.at160, h.at1792, h.at1824, h.at1856, h.at1888, h.at1920, h.at1952, h.at1984, h.at2016, h.at2048, h.at192, h.at0, h.at224, h.at1216, h.at1248, h.at1088, h.at1280]

end CycleSubmission.ProductMeaning
