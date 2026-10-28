import Challenge.Ripemd160.Submission.Local20261028.ColdPaddingCore2
import Challenge.Ripemd160.Submission.Local20261028.FirstComplete
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Framed32
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PaddingTrace FirstEntry

theorem copied_memory (input : ByteArray) :
    (padCopied input).memory = FirstSpec.copiedMemory input := by
  unfold FirstSpec.copiedMemory
  change MachineState.writeBytes (padLengthReady input).memory (MachineState.readPadded input 0 input.size) Padding.messageOffset = _
  have hm : (padLengthReady input).memory = ByteArray.empty := rfl
  rw [hm,Memory.readPadded_zero_size]
  rfl

theorem copied_active (input : ByteArray) (h32 : input.size = 32) :
    (padCopied input).activeWords = UInt256.ofNat 34 := by
  change UInt256.ofNat (MachineState.activeWordsAfter 0 1056 input.size) = _
  rw [h32]
  rfl

def prepared (input : ByteArray) : State := FirstCore.prepared (FirstRead.result (high (padCopied input)))
def resultHash (input : ByteArray) := CoreFunctional.result (prepared input).memory FirstCore.initialHash
def result (input : ByteArray) (rho : List UInt256) :=
  Return32Serialize.result (prepared input) (resultHash input) (UInt256.ofNat 1056)
    (Word.ofUInt32 FirstCore.initialHash.h2) (NormalPrepare.masks rho)

def gasSteps (input : ByteArray) (h32 : input.size = 32) (rho : List UInt256) (hs : rho.length ≤ 20) :
    GasSteps (StackTail.append (padFramed input) rho) (result input rho) := by
  let s := padCopied input
  have e : Env s := ⟨rfl,rfl,rfl,deployAddress_not_precompile⟩
  have ha : 34 ≤ s.activeWords.toNat := by rw [copied_active input h32]; decide
  have ga := align s e (FirstCore.frame (UInt256.ofNat 32) rho)
    (by simp [FirstCore.frame,StaggerPersistentFrame.frame,NormalPrepare.masks]; omega) h32
  have gp := special s e rho (by omega) ha
  have gc := FirstReadGas.complete (high s) (UInt256.ofNat 9949) rho (by omega)
    e.running ha e.code e.fork e.noPrecompile
  have ep : Env (prepared input) := ⟨e.code,e.fork,e.running,e.noPrecompile⟩
  have gd := dispatch (prepared input) ep (resultHash input) (UInt256.ofNat 1056)
    (Word.ofUInt32 FirstCore.initialHash.h2) (NormalPrepare.masks rho) (by simp [NormalPrepare.masks]; omega)
  have go := Return32Serialize.gasSteps (prepared input) (UInt256.ofNat 1056)
    (Word.ofUInt32 FirstCore.initialHash.h2) (resultHash input) rho (by omega)
    e.running e.code e.fork e.noPrecompile h32
  have g := ga.trans (gp.trans (gc.trans (gd.trans go)))
  exact g.cast (by simp only [StackTail.append,padFramed,initialFrame,copiedLimit,h32,FirstCore.frame,NormalPrepare.masks,StaggerPersistentFrame.frame,List.cons_append,List.nil_append]; rfl) rfl

theorem returned_spec (input : ByteArray) (h32 : input.size = 32) (rho : List UInt256) :
    (result input rho).hReturn = Challenge.Ripemd160.spec input := by
  apply Return32Serialize.returned_spec_of_hashArray
  apply FirstMessageSpec.hash_spec (high (padCopied input)) input h32
  change PairedScheduleMemory.writeWord (padCopied input).memory 162 FirstInitial.highWord = _
  rw [copied_memory]

theorem correct (input : ByteArray) (h32 : input.size = 32) (rho : List UInt256) (hs : rho.length ≤ 20)
    (prefixTrace : GasSteps (initialState submissionBytecode input 0) (StackTail.append (padFramed input) rho)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas → Eval (initialState submissionBytecode input gas) (.returned (Challenge.Ripemd160.spec input)) := by
  exact FirstComplete.eval_of_returned_trace _ _ _ (prefixTrace.trans (gasSteps input h32 rho hs))
    rfl rfl (returned_spec input h32 rho)
#print axioms gasSteps
#print axioms correct
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Framed32
