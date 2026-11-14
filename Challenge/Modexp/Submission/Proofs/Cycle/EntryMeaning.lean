import Challenge.Modexp.Submission.Proofs.Cycle.NormalizeMeaning
import Challenge.Modexp.Submission.Proofs.Cycle.Execution.Entry
import Challenge.Modexp.Submission.Proofs.Cycle.InputWords
import Challenge.Modexp.Submission.Proofs.Cycle.LimbMemory
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
  [f.pbi,f.hd,f.w3,f.ent,f.m32,UInt256.ofNat (2^256-1),f.m128,f.m64,
   f.m0,f.tl,f.m96,f.inv,f.tn,f.aprev,f.counter,f.ret]++f.tail
set_option linter.unusedVariables false in
def cells (mem : ByteArray) (f : Caller) : List (Nat × UInt256) :=
  [(1344,ordinary mem 0 0),(1376,ordinary mem 0 1),
   (1600,ordinary mem 0 8),(1568,ordinary mem 0 7),
   (768,scaled mem 2368 0),(32,scaled mem 2368 3),(64,scaled mem 2368 4),
   (128,scaled mem 2368 6)]
def cacheFrame (_inv : UInt256) (a _b n : Nat → UInt256) (count : UInt256) (rest : List UInt256) : List UInt256 :=
 [(n 2),(n 6),(n 4),(a 1),(a 2),(n 5),(n 7),CycleSubmission.WordArithmetic.P,(n 8),(n 1),(a 5),(n 0),(n 3),(a 7),(a 8),count]++rest
def result (s : State) (f : Caller) : State :=
  {s with
    pc := UInt256.ofNat 3476
    memory := storeCells s.memory (cells s.memory f)
    stack := cacheFrame (MachineState.readWord s.memory 2720)
      (scaled s.memory 2368) (fun _ => UInt256.ofNat 0) (ordinary s.memory 0) (UInt256.ofNat 0-f.counter) (saved f).tail}
theorem model_eq (s : State) (f : Caller) :
    entryModel s f.pbi f.hd f.w3 f.ent f.m32 (UInt256.ofNat (2^256-1))
      f.m128 f.m64 f.m0 f.tl f.m96 f.inv f.tn f.aprev f.counter f.ret f.tail = result s f := by
  have h240 : UInt256.shiftRight (UInt256.ofNat (2^256-1)) (UInt256.ofNat 16) = UInt256.ofNat (2^240-1) := by decide
  have h251 : UInt256.shiftRight (UInt256.lnot (UInt256.ofNat 0)) (UInt256.ofNat 5) = UInt256.ofNat (2^251-1) := by decide
  simp (disch := decide) only [entryModel,result,cells,storeCells,writeCell,
    readStore,readWord_writeWord,CycleSubmission.Prepared.Arithmetic.read_disjoint,h240,h251,
    Nat.reduceLT,Nat.reduceEqDiff,Nat.reduceMul,Nat.reduceSub,Nat.reduceAdd,↓reduceIte,
    cacheFrame,CycleSubmission.SquareMeaning.frame0,CycleSubmission.WordArithmetic.P,HistoricalSearch.CRTColumn.residueModulus,saved,scaled,scaledLow,scaledTop,ordinary,low,top,List.set,
    List.cons_append,List.nil_append,List.tail_cons,CycleSubmission.Prepared.Arithmetic.andC]
theorem run (s : State) (f : Caller) (hcap : f.tail.length ≤ 959)
    (hact : 88 ≤ s.activeWords.toNat) :
    runInstructions entryProgram {s with pc := UInt256.ofNat 3318,stack := saved f} =
      some (result s f) := by
  have h := entry_run s f.pbi f.hd f.w3 f.ent f.m32 (UInt256.ofNat (2^256-1))
    f.m128 f.m64 f.m0 f.tl f.m96 f.inv f.tn f.aprev f.counter f.ret f.tail (by omega) hact
  rw [model_eq] at h
  exact h
theorem memory_output (s : State) (f : Caller) :
    LimbMemory.Holds (result s f).memory
      (MachineState.readWord s.memory 2720) (scaled s.memory 2368)
      (fun _ => UInt256.ofNat 0) (ordinary s.memory 0) := by
  constructor <;>
    simp (disch := decide) only [result,cells,storeCells,writeCell,
      readStore,readWord_writeWord]
end CycleSubmission.EntryMeaning
#print axioms CycleSubmission.EntryMeaning.model_eq
#print axioms CycleSubmission.EntryMeaning.run
#print axioms CycleSubmission.EntryMeaning.memory_output
