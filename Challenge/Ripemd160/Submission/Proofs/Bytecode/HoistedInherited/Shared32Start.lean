import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Trace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Alignment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Spec
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.PaddingTrace

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Start
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open HoistedInherited.Shared32Scratch HoistedInherited.Shared32Sites Paired144WordRound

def maskRho : List UInt256 := [DenseScheduleTemplate.mask8, DenseScheduleTemplate.mask16]
def frame : List UInt256 := StaggerPersistentFrame.frame StackRunBridge.initialHashState
  (UInt256.ofNat 1056) (UInt256.ofNat 32) maskRho
def entryFrame : List UInt256 := StaggerPersistentFrame.frame StackRunBridge.initialHashState
  (UInt256.ofNat 1056) (UInt256.ofNat 32) maskRho
/-- After the 32-byte block the continuation slot holds the output entry, so the single block finishes. -/
def bodyFrame : List UInt256 := StaggerPersistentFrame.frame StackRunBridge.initialHashState
  (UInt256.ofNat 1056) (UInt256.ofNat 9667) maskRho

theorem rounded_32 : PadLimitArithmetic.rounded (UInt256.ofNat 32) = UInt256.ofNat 64 := by decide

theorem entry_frame_eq (input : ByteArray) (h32 : input.size = 32) :
    HoistedInherited.PaddingTrace.initialFrame input = entryFrame := by
  simp only [HoistedInherited.PaddingTrace.initialFrame, HoistedInherited.PaddingTrace.copiedLimit, h32]
  rfl

def tableState (input : ByteArray) : State :=
  {HoistedInherited.PaddingTrace.padCopied input with
    activeWords := UInt256.ofNat 35
    memory := HoistedInherited.Shared32Table.tableMemory (copiedMemory input)}

theorem table_active (input : ByteArray) :
    (tableState input).activeWords = UInt256.ofNat 35 := rfl

theorem padded_eq (input : ByteArray) (h32 : input.size = 32) :
    Padding.paddedWord input = UInt256.ofNat 64 := by
  rw [Padding.paddedWord_eq input (by rw [h32]; decide), h32]
  rfl

theorem frame_eq (input : ByteArray) (h32 : input.size = 32) :
    HoistedInherited.PaddingTrace.initialFrame input = frame := by
  exact entry_frame_eq input h32

theorem copied_memory (input : ByteArray) :
    (HoistedInherited.PaddingTrace.padCopied input).memory = copiedMemory input := by
  change MachineState.writeBytes ByteArray.empty
    (MachineState.readPadded input 0 input.size) 1056 = copiedMemory input
  rw [Memory.readPadded_zero_size]
  rfl

theorem copied_active (input : ByteArray) (h32 : input.size = 32) :
    (HoistedInherited.PaddingTrace.padCopied input).activeWords = UInt256.ofNat 34 := by
  change UInt256.ofNat (MachineState.activeWordsAfter 0 1056 input.size) = UInt256.ofNat 34
  rw [h32]
  rfl

theorem copied_low (input : ByteArray) :
    (MachineState.readWord (HoistedInherited.PaddingTrace.padCopied input).memory 0).toNat < 2 ^ 32 := by
  rw [copied_memory]
  unfold copiedMemory
  rw [Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by decide))]
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data]
  decide

def gasSteps_align (input : ByteArray) (h32 : input.size = 32) :
    GasSteps (HoistedInherited.PaddingTrace.padFramed input) (HoistedInherited.PaddingTrace.padGuardTaken input) := by
  exact HoistedInherited.Shared32Alignment.gasSteps (HoistedInherited.PaddingTrace.padCopied input)
    ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩ (HoistedInherited.PaddingTrace.initialFrame input)
    (by rw [HoistedInherited.PaddingTrace.initialFrame_length]; decide) h32

def gasSteps (input : ByteArray) (h32 : input.size = 32)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (HoistedInherited.Execution.atPC input 246)) :
    GasSteps (initialState submissionBytecode input 0) (atState (tableState input) 824 bodyFrame) := by
  have hfit : CalldataFits input := by change input.size < 2 ^ 64; rw [h32]; decide
  let s := HoistedInherited.PaddingTrace.padCopied input
  have e : Env s := ⟨rfl, rfl, rfl, deployAddress_not_precompile⟩
  have hframe : HoistedInherited.PaddingTrace.initialFrame input = entryFrame := entry_frame_eq input h32
  have hactive : s.activeWords = UInt256.ofNat 34 := copied_active input h32
  have g0 := (HoistedInherited.Main.gasSteps_initialize input entryPrefix).trans
    ((HoistedInherited.PaddingTrace.gasSteps_enterPad input).trans ((HoistedInherited.PaddingTrace.gasSteps_lengthReady input).trans
      ((HoistedInherited.PaddingTrace.gasSteps_lengthCopy input hfit).trans (HoistedInherited.PaddingTrace.gasSteps_push input))))
  have g1 : GasSteps (HoistedInherited.PaddingTrace.padFramed input) (atState s 143 entryFrame) := by
    simpa only [HoistedInherited.PaddingTrace.padGuardTaken, HoistedInherited.PaddingTrace.padGuardMiss, hframe, atState, s] using
      gasSteps_align input h32
  have g4 := HoistedInherited.Shared32Trace.gasSteps_sparse s e factorPlusWord (UInt256.ofNat 4294967295)
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3)
    (fusedCoefficientWord 0 2)
    (Word.ofUInt32 StackRunBridge.initialHashState.h4) (Word.ofUInt32 StackRunBridge.initialHashState.h3)
    (Word.ofUInt32 StackRunBridge.initialHashState.h2) (Word.ofUInt32 StackRunBridge.initialHashState.h1)
    (Word.ofUInt32 StackRunBridge.initialHashState.h0) (UInt256.ofNat 32) [] (by decide)
    (by rw [copied_memory]; have hh := HoistedInherited.Shared32Scratch.copiedMemory_size input (by omega); omega)
    (by rw [copied_memory]; intro a ha hb; exact HoistedInherited.Shared32Scratch.copiedMemory_zero input a (by omega))
    hactive (by decide) h32 rfl
  have g5 := HoistedInherited.Shared32Trace.gasSteps_table s e factorPlusWord
    (fusedModulusWord 5 7) (fusedModulusWord 8 5) (fusedCoefficientWord 0 3)
    (fusedCoefficientWord 0 2)
    (Word.ofUInt32 StackRunBridge.initialHashState.h4) (Word.ofUInt32 StackRunBridge.initialHashState.h3)
    (Word.ofUInt32 StackRunBridge.initialHashState.h2) (Word.ofUInt32 StackRunBridge.initialHashState.h1)
    (Word.ofUInt32 StackRunBridge.initialHashState.h0) (UInt256.ofNat 9667) [] (by decide) hactive
  have hm : sparseMemory s.memory = PairedScheduleMemory.writeWord s.memory 162 highWord := by
    rw [show s.memory = copiedMemory input from copied_memory input]
    exact copiedMemory_sparse input (by omega)
  rw [hm] at g4
  have g := g0.trans (g1.trans (g4.trans g5))
  simpa only [atState, tableState, s, copied_memory, frame, bodyFrame, maskRho,
    StaggerPersistentFrame.frame, HoistedInherited.Pair13Endian.stk, List.cons_append, List.nil_append] using g

theorem table_ready (input : ByteArray) (h32 : input.size = 32) :
    StaggerMessage.Ready (tableState input).memory
      (fun k => (CompressionCorrect.schedule (Padding.paddedMessage input) 0)[k]!) := by
  apply HoistedInherited.Shared32Table.tableMemory_ready _
    (HoistedInherited.PoolInvariant.clear_of_zero _ (HoistedInherited.Shared32Scratch.copiedMemory_zero input))
    (HoistedInherited.PoolInvariant.clearV2_of_zero _ (HoistedInherited.Shared32Scratch.copiedMemory_zero input))
  exact StaggerMessage.ready_dual0 (copiedMemory input) (HoistedInherited.Shared32Table.words (copiedMemory input)) _
    (HoistedInherited.Shared32Table.words_clean (copiedMemory input) 6 (by decide) (by decide))
    (HoistedInherited.Shared32Spec.ready_spec input h32)

#print axioms gasSteps
#print axioms table_ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Shared32Start
