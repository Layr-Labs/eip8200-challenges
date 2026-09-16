import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentFrame
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdOrdinaryPrepare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopSites
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration ColdHighPaddingMemory StaggerPersistentFrame

def maskRho : List UInt256 := [DenseScheduleTemplate.mask8,DenseScheduleTemplate.mask16]
/-- What the low block really leaves: the six stores over the base the calldata copy actually
produces (`zeroSuffix`), not over the model's fully cleared `zeroMemory`. -/
def lowState (input : ByteArray) (i : Nat) : State :=
  {states input i with memory:=StaggerTablePad.padRealChain (states input i).memory (UInt256.ofNat input.size)}
def paddedState (input : ByteArray) (i : Nat) : State :=
  {states input i with memory:=finalMemory input i, activeWords:=PaddingTraceGeneral.lengthActive input (states input i).activeWords (PaddingTrace.lengthStop input)}
def tableState (input : ByteArray) (i : Nat) : State :=
  {paddedState input i with memory:=ColdHighReady.tableMemory input i, activeWords:=DenseScheduleTemplate.loadedActiveWords (paddedState input i) (UInt256.ofNat (messagePointer i))}

theorem large_branch (input : ByteArray) (hfit : CalldataFits input) (hlarge : 5214 ≤ input.size) :
    ¬UInt256.isTrue (StaggerPad.highZero (UInt256.ofNat input.size)) := by
  intro h
  have hn := (StaggerPad.highZero_true_iff _).mp h
  rw [size_word_toNat input hfit] at hn
  omega

theorem tableState_active (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i<DriverTrace.blockCount input) : 35≤(tableState input i).activeWords.toNat :=
  Stagger144Active.loaded_active_ge35 (paddedState input i) (messagePointer i)
    (messagePointer_lower i) (messagePointer_bound input hfit i hi)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighTrace
