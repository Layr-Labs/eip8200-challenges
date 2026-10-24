import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Entry
import Challenge.Modexp.Submission.Proofs.Cycle.SquareFrames
import Challenge.Modexp.Submission.Proofs.Cycle.InputWords
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
namespace CycleSubmission.EntryMeaning
open EvmSemantics EvmSemantics.EVM
open CycleSubmission.InputWords CycleSubmission.Execution
open HistoricalSearch.CRTMemoryCells Challenge.EvmProof.Memory
open CycleSubmission.NormalizeMeaning (readStore)
open Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

structure Caller where
  pbi : UInt256
  hd : UInt256
  w3 : UInt256
  ent : UInt256
  m32 : UInt256
  m128 : UInt256
  m64 : UInt256
  m0 : UInt256
  tl : UInt256
  m96 : UInt256
  inv : UInt256
  tn : UInt256
  aprev : UInt256
  counter : UInt256
  ret : UInt256
  tail : List UInt256

def saved (f : Caller) : List UInt256 :=
  [f.pbi, f.hd, f.w3, f.ent, f.m32, UInt256.ofNat (2^256-1), f.m128, f.m64,
   f.m0, f.tl, f.m96, f.inv, f.tn, f.aprev, f.counter, f.ret] ++ f.tail

def cells (mem : ByteArray) (f : Caller) : List (Nat × UInt256) :=
  [(1728, f.counter), (1344, ordinary mem 0 0), (1376, ordinary mem 0 1),
   (1600, ordinary mem 0 8), (1568, ordinary mem 0 7),
   (768, scaled mem 2368 0), (32, scaled mem 2368 3), (64, scaled mem 2368 4),
   (96, scaled mem 2368 5), (128, scaled mem 2368 6), (160, scaled mem 2368 7)]

def result (s : State) (f : Caller) : State :=
  {s with
    pc := UInt256.ofNat 6152
    memory := storeCells s.memory (cells s.memory f)
    stack := CycleSubmission.SquareMeaning.frame0 (MachineState.readWord s.memory 2720)
      (scaled s.memory 2368) (fun _ => UInt256.ofNat 0) (ordinary s.memory 0) (saved f)}

theorem model_eq (s : State) (f : Caller) :
    entryModel s f.pbi f.hd f.w3 f.ent f.m32 (UInt256.ofNat (2^256-1))
      f.m128 f.m64 f.m0 f.tl f.m96 f.inv f.tn f.aprev f.counter f.ret f.tail = result s f := by
  simp (disch := decide) only [entryModel, readStore]
  rfl

theorem run (s : State) (f : Caller) (hcap : f.tail.length ≤ 960)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram {s with pc := UInt256.ofNat 5964, stack := saved f} =
      some (result s f) := by
  have h := entry_run s f.pbi f.hd f.w3 f.ent f.m32 (UInt256.ofNat (2^256-1))
    f.m128 f.m64 f.m0 f.tl f.m96 f.inv f.tn f.aprev f.counter f.ret f.tail hcap hact
  rw [model_eq] at h
  exact h

theorem memory_output (s : State) (f : Caller) :
    CycleSubmission.SquareMeaning.Memory0 (result s f).memory
      (MachineState.readWord s.memory 2720) (scaled s.memory 2368)
      (fun _ => UInt256.ofNat 0) (ordinary s.memory 0) := by
  constructor <;>
    simp (disch := decide) only [result, cells, storeCells, writeCell,
      readStore, readWord_writeWord]

end CycleSubmission.EntryMeaning
