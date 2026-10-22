import Challenge.Modexp.Submission.Proofs.CRT.CRTAdapterMeaning
import Challenge.Modexp.Submission.Proofs.CRT.CRTLoopArithmetic
import Challenge.Modexp.Submission.Proofs.CRT.CRTControl
import Challenge.Modexp.Submission.Proofs.CRT.StateIndependence
import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedFrames
import Challenge.Modexp.Submission.Proofs.Fast.TnM128SquareExit
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 40000
set_option maxHeartbeats 500000

namespace HistoricalSearch.CRTLoopFrames
open EvmSemantics EvmSemantics.EVM
open HistoricalSearch.GeneratedColumns HistoricalSearch.GeneratedArithmetic
open HistoricalSearch.ConcreteArithmetic
open HistoricalSearch.CRTAdapterMeaning HistoricalSearch.CRTLoopArithmetic
open HistoricalSearch.CRTControl
open Challenge.Modexp.Submission.Proofs.Fast

structure Frame where
  w3 : UInt256
  tl : UInt256
  inv : UInt256
  m0 : UInt256
  m96 : UInt256
  m64 : UInt256
  m32 : UInt256
  m128 : UInt256
  aprev : UInt256
  counter : UInt256
  ret : UInt256
  rest : List UInt256

def saved (f : Frame) : List UInt256 :=
  [UInt256.ofNat 0, UInt256.ofNat 5297, f.w3, UInt256.ofNat 3643, f.m32,
   CiosCached.allOnes, f.m128, f.m64, f.m0, f.tl, f.m96, f.inv,
   UInt256.ofNat 0, f.aprev, f.counter, f.ret] ++ f.rest

def cache (n : Nat → UInt256) (minv : UInt256) (f : Frame) : List UInt256 :=
  [modulusWord, n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7, n 8,
   maskWord, minv] ++ saved f

def atCache (s : State) (mem : ByteArray) (pc : Nat)
    (n : Nat → UInt256) (minv : UInt256) (f : Frame) : State :=
  {s with pc := UInt256.ofNat pc, memory := mem, stack := cache n minv f}

def entryState (s : State) (mem : ByteArray) (f : Frame) (pbi ent : UInt256) : State :=
  entryModel {s with memory := mem} pbi (UInt256.ofNat 5297) f.w3 ent f.m32
    CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0)
    f.aprev f.counter f.ret f.rest

theorem entry_normalize (s : State) (mem : ByteArray) (f : Frame) (pbi ent : UInt256) :
    entryState s mem f pbi ent = atCache s (entryMemory mem f.counter) 5859
      (inputWord mem 0) (MachineState.readWord mem 2720) f := by
  unfold entryState
  rw [entry_model]
  rfl

def afterKernel (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) : State :=
  result {s with memory := mem} minv n (saved f)

theorem step16_pc (s : State) (carry minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) :
    (ColumnMemory.step 16 s carry minv n rest).pc = UInt256.ofNat 8129 := by rfl

theorem step16_stack (s : State) (carry minv : UInt256) (n : Nat → UInt256) (rest : List UInt256) :
    (ColumnMemory.step 16 s carry minv n rest).stack =
      [modulusWord, n 0, n 1, n 2, n 3, n 4, n 5, n 6, n 7, n 8, maskWord, minv] ++ rest := by rfl

theorem afterKernel_pc (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    (afterKernel s mem n minv f).pc = UInt256.ofNat 8129 := by
  unfold afterKernel result
  rw [show 17 = 16+1 from rfl, ColumnSequence.states_succ, step16_pc]

theorem afterKernel_stack (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    (afterKernel s mem n minv f).stack = cache n minv f := by
  unfold afterKernel result
  rw [show 17 = 16+1 from rfl, ColumnSequence.states_succ, step16_stack]
  rfl

theorem afterKernel_memory (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    (afterKernel s mem n minv f).memory = (result {s with memory := mem} minv n []).memory :=
  StateIndependence.states_memory _ _ minv n _ [] rfl

theorem metadata_update (a b : State) (h : StateIndependence.metadata a = StateIndependence.metadata b)
    (pc : UInt256) (mem : ByteArray) (stack : List UInt256) :
    {a with pc := pc, memory := mem, stack := stack} =
      {b with pc := pc, memory := mem, stack := stack} := by
  exact congrArg (fun x : State => {x with pc := pc, memory := mem, stack := stack}) h

theorem state_eq (a b : State) (h : StateIndependence.metadata a = StateIndependence.metadata b)
    (hp : a.pc = b.pc) (hm : a.memory = b.memory) (hs : a.stack = b.stack) : a = b := by
  have he := metadata_update a b h b.pc b.memory b.stack
  calc
    a = {a with pc := b.pc, memory := b.memory, stack := b.stack} := by rw [←hp, ←hm, ←hs]
    _ = {b with pc := b.pc, memory := b.memory, stack := b.stack} := he
    _ = b := rfl

theorem afterKernel_normalize (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    afterKernel s mem n minv f = atCache s (result {s with memory := mem} minv n []).memory 8129 n minv f := by
  apply state_eq
  · exact StateIndependence.states_metadata {s with memory := mem} minv n (saved f) 17 (by decide)
  · exact afterKernel_pc s mem n minv f
  · exact afterKernel_memory s mem n minv f
  · exact afterKernel_stack s mem n minv f

def overflowState (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) : State :=
  conditionalModel (overflowModel {s with memory := mem} modulusWord
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv
    (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32
    CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0)
    f.aprev f.counter f.ret f.rest)

theorem overflow_normalize (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    overflowState s mem n minv f = atCache s (checkedMemory mem)
      (if (UInt256.shiftRight (rawDigits mem 8) (UInt256.ofNat 192)).toNat = 0 then 8145 else 8800)
      n minv f := by
  by_cases hz : (UInt256.shiftRight (MachineState.readWord mem 1600) (UInt256.ofNat 192)).toNat = 0 <;>
    simp [overflowState, conditionalModel, overflowModel, checkedMemory, CRTMemoryCells.writeCell,
      rawDigits, atCache, cache, saved, hz, Challenge.EvmProof.Word.succ_ofNat_mod]

def countState (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) : State :=
  conditionalModel (countModel {s with memory := mem} modulusWord
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv
    (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32
    CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0)
    f.aprev f.counter f.ret f.rest)

theorem count_normalize (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    countState s mem n minv f = atCache s mem
      (if (MachineState.readWord mem 1728).toNat = 0 then 8800 else 8154) n minv f := by
  by_cases hz : (MachineState.readWord mem 1728).toNat = 0 <;>
    simp [countState, countModel, conditionalModel, atCache, cache, saved,
      Challenge.EvmProof.Word.word_toNat_isZero, hz, Challenge.EvmProof.Word.succ_ofNat_mod]

def retainState (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) : State :=
  resumeModel (retainModel {s with memory := mem} modulusWord
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv
    (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32
    CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0)
    f.aprev f.counter f.ret f.rest)

theorem retain_normalize (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    retainState s mem n minv f = atCache s (retainedMemory mem) 5859 n minv f := by
  unfold retainState
  rw [show maskWord = UInt256.ofNat (2^244-1) from rfl, retain_model]
  rfl

def atOld (s : State) (mem : ByteArray) (pc : Nat) (tn pbi ent : UInt256) (f : Frame) : State :=
  TnM128SquareExit.frameAt tn f.m128 pc s mem 8 pbi f.w3 ent f.tl f.inv
    f.m0 f.m96 f.m64 f.m32 f.aprev f.counter f.ret f.rest

def exitState (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) : State :=
  jumpModel (exitModel {s with memory := mem} modulusWord
    (n 0) (n 1) (n 2) (n 3) (n 4) (n 5) (n 6) (n 7) (n 8) maskWord minv
    (UInt256.ofNat 0) (UInt256.ofNat 5297) f.w3 (UInt256.ofNat 3643) f.m32
    CiosCached.allOnes f.m128 f.m64 f.m0 f.tl f.m96 f.inv (UInt256.ofNat 0)
    f.aprev f.counter f.ret f.rest)

def exitFrame (mem : ByteArray) (f : Frame) : Frame :=
  {f with aprev := cachedTop mem, counter := MachineState.readWord mem 1728}

theorem exit_normalize (s : State) (mem : ByteArray) (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    exitState s mem n minv f = atOld s (exitMemory mem) 3942 (MachineState.readWord mem 1760)
      (UInt256.ofNat 0) (UInt256.ofNat 3643) (exitFrame mem f) := by
  unfold exitState
  rw [exit_model]
  rfl

theorem cache_length (n : Nat → UInt256) (minv : UInt256) (f : Frame) :
    (cache n minv f).length = 28+f.rest.length := by
  simp only [cache, saved, List.length_append, List.length_cons, List.length_nil]
  omega

theorem saved_length (f : Frame) : (saved f).length = 16+f.rest.length := by
  simp only [saved, List.length_append, List.length_cons, List.length_nil]

#print axioms entry_normalize
#print axioms afterKernel_memory
#print axioms afterKernel_normalize
#print axioms overflow_normalize
#print axioms count_normalize
#print axioms retain_normalize
#print axioms exit_normalize
end HistoricalSearch.CRTLoopFrames
