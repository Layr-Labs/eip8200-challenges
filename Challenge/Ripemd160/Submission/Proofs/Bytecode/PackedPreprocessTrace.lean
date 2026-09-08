import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionGapSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessByteSwap
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessPreservation
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessSpreadSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessValues

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

/-!
# Complete located packed preprocessing trace

This module joins the three artifact regions executed before the packed
rounds: the gap-clearing store, two-word byte swap, and sixteen descending
spread stores.  Memory expansion is taken from the two actual source MLOADs;
the trace does not add an active-memory premise to the compression kernel.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessTrace

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM

/-- State after the explicit gap clear.  The source pointer stays on top for
the byte-swap load sequence. -/
def clearState (s : State) (source : Nat) (rest : List UInt256) : State :=
  PackedCompressionGapSite.gapCleared s (UInt256.ofNat source :: rest)

/-- State after both aligned words have been loaded, byte-swapped, and stored.
Its active-word count is the exact count produced by the two source MLOADs. -/
def swappedState (s : State) (source : Nat) (rest : List UInt256) : State :=
  PackedPreprocessByteSwap.byteSwapReturned (clearState s source rest)
    PackedPreprocessByteSwap.byteSwapSite.endPC source rest

def preprocessEntry (s : State) (source : Nat)
    (rest : List UInt256) : State :=
  PackedCompressionGapSite.gapEntry s (UInt256.ofNat source :: rest)

def preprocessReturned (s : State) (source : Nat)
    (rest : List UInt256) : State :=
  PackedPreprocessSpreadSite.spreadReturned (swappedState s source rest) rest

@[simp] theorem preprocessReturned_pc (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).pc = UInt256.ofNat 784 := by
  rfl

@[simp] theorem preprocessReturned_stack (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).stack = rest := by
  rfl

@[simp] theorem preprocessReturned_memory (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).memory =
      PackedPreprocessLayout.spreadMemory
        (PackedPreprocessLayout.packedBaseMemory
          (clearState s source rest).memory
          (PackedPreprocessByteSwap.inputWord0
            (clearState s source rest).memory source)
          (PackedPreprocessByteSwap.inputWord1
            (clearState s source rest).memory source)) := by
  rfl

@[simp] theorem preprocessReturned_activeWords (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).activeWords =
      PackedPreprocessByteSwap.loadedActiveWords
        (clearState s source rest) source := by
  rfl

/-- The two source loads reach at least word 18 because packed input begins at
byte 512.  The later low-memory stores cannot reduce that active-word count. -/
theorem preprocessReturned_activeWords_ge_18 (s : State) (source : Nat)
    (rest : List UInt256) (hsource : 512 ≤ source)
    (hnowrap : source + 64 < 2 ^ 256) :
    18 ≤ (preprocessReturned s source rest).activeWords.toNat := by
  rw [preprocessReturned_activeWords,
    PackedPreprocessByteSwap.loadedActiveWords_toNat
      (clearState s source rest) source hnowrap]
  have hlast : 17 ≤ (source + 32 + 32 - 1) / 32 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 32)).2
    omega
  unfold MachineState.activeWordsAfter
  rw [if_neg (by norm_num : (32 : Nat) ≠ 0)]
  exact (by omega : 18 ≤ (source + 32 + 32 - 1) / 32 + 1).trans
    (Nat.le_max_right _ _)

@[simp] theorem preprocessReturned_executionEnv (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).executionEnv = s.executionEnv := by
  rfl

@[simp] theorem preprocessReturned_halt (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).halt = s.halt := by
  rfl

@[simp] theorem preprocessReturned_callStack (s : State) (source : Nat)
    (rest : List UInt256) :
    (preprocessReturned s source rest).callStack = s.callStack := by
  rfl

private theorem clearState_eq_byteSwapEntry (s : State) (source : Nat)
    (rest : List UInt256) :
    clearState s source rest =
      PackedPreprocessByteSwap.byteSwapEntry (clearState s source rest)
        PackedPreprocessByteSwap.byteSwapSite.startPC source rest := by
  simp [clearState, PackedCompressionGapSite.gapCleared,
    PackedPreprocessByteSwap.byteSwapEntry]

private theorem swappedState_eq_spreadEntry (s : State) (source : Nat)
    (rest : List UInt256) :
    swappedState s source rest =
      PackedPreprocessSpreadSite.spreadEntry (swappedState s source rest)
        rest := by
  simp [swappedState, clearState,
    PackedPreprocessByteSwap.byteSwapReturned,
    PackedPreprocessSpreadSite.spreadEntry]

/-- Clearing the low scratch gap preserves every full word at or above the
aligned packed-message region. -/
theorem clearState_readWord_above (s : State) (source : Nat)
    (rest : List UInt256) (address : Nat) (haddress : 352 ≤ address) :
    MachineState.readWord (clearState s source rest).memory address =
      MachineState.readWord s.memory address := by
  change MachineState.readWord
      (MachineState.writeBytes s.memory
        (Data.Bytes.natToBytesPadded 0 32) 272) address =
    MachineState.readWord s.memory address
  rw [Memory.readWord_writeBytes_disjoint]
  right
  simp [Data.Bytes.natToBytesPadded, ByteArray.size]
  omega

theorem clearState_expectedWord (s : State) (source i : Nat)
    (rest : List UInt256) (hsource : 512 ≤ source)
    (hi : i < 16) (hnowrap : source + 64 < 2 ^ 256) :
    ScheduleCorrect.expectedWord (clearState s source rest).memory
        (PackedScheduleMemory.naturalp source) i =
      ScheduleCorrect.expectedWord s.memory
        (PackedScheduleMemory.naturalp source) i := by
  have haddress :
      352 ≤ (Schedule.loadOffsetWord
        (PackedScheduleMemory.naturalp source) i).toNat := by
    rw [PackedScheduleMemory.loadOffsetWord_toNat source i hi hnowrap]
    omega
  unfold ScheduleCorrect.expectedWord Schedule.readLEWord
  rw [clearState_readWord_above s source rest _ haddress]

/-- The actual base-memory operand at each spread site is the corresponding
little-endian word of the untouched source block. -/
theorem spreadValue_eq_expected (s : State) (source i : Nat)
    (rest : List UInt256) (hsource : 512 ≤ source)
    (hi : i < 16) (hnowrap : source + 64 < 2 ^ 256) :
    PackedPreprocessLayout.spreadValue
        (swappedState s source rest).memory i =
      ScheduleCorrect.expectedWord s.memory
        (PackedScheduleMemory.naturalp source) i := by
  rw [show (swappedState s source rest).memory =
      PackedPreprocessLayout.packedBaseMemory
        (clearState s source rest).memory
        (MachineState.readWord (clearState s source rest).memory source)
        (MachineState.readWord (clearState s source rest).memory
          (source + 32)) by
    rfl]
  rw [PackedPreprocessValues.spreadValue_packedBaseMemory
    (clearState s source rest).memory source i hi hnowrap]
  exact clearState_expectedWord s source i rest hsource hi hnowrap

theorem preprocessReturned_gap (s : State) (source : Nat)
    (rest : List UInt256) :
    PackedGapInvariant.GapZero (preprocessReturned s source rest).memory := by
  have hclear := PackedCompressionGapSite.gapCleared_gapZero s
    (UInt256.ofNat source :: rest)
  have hpreserved := PackedPreprocessPreservation.preprocessing_gap
    (clearState s source rest).memory
    (PackedPreprocessByteSwap.inputWord0
      (clearState s source rest).memory source)
    (PackedPreprocessByteSwap.inputWord1
      (clearState s source rest).memory source) hclear
  rw [preprocessReturned_memory]
  exact hpreserved

theorem preprocessReturned_read_above (s : State) (source : Nat)
    (rest : List UInt256) (address : Nat) (haddress : 352 ≤ address) :
    MachineState.readWord (preprocessReturned s source rest).memory address =
      MachineState.readWord s.memory address := by
  have hpre := PackedPreprocessPreservation.preprocessing_read_above
    (clearState s source rest).memory
    (PackedPreprocessByteSwap.inputWord0
      (clearState s source rest).memory source)
    (PackedPreprocessByteSwap.inputWord1
      (clearState s source rest).memory source)
    address haddress
  have hclear := clearState_readWord_above s source rest address haddress
  rw [preprocessReturned_memory]
  exact hpre.trans hclear

/-- Complete concrete preprocessing trace from the first gap instruction at
PC 539 through the state immediately after the spread POP at PC 784. -/
def gasSteps_preprocess (s : State) (source : Nat) (rest : List UInt256)
    (hsource : 512 ≤ source) (hnowrap : source + 64 < 2 ^ 256)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (preprocessEntry s source rest)
      (preprocessReturned s source rest) := by
  have hgap := PackedCompressionGapSite.gasSteps_gapPath s
    (UInt256.ofNat source :: rest)
    (by simp only [List.length_cons]; omega) hcode hfork hrun hnp
  have hartifactCode :
      (clearState s source rest).executionEnv.code =
        Artifact.submissionArtifact.code := by
    change s.executionEnv.code = submissionBytecode
    exact hcode
  have hclearFork : (clearState s source rest).fork = .Osaka := by
    simpa [clearState, PackedCompressionGapSite.gapCleared] using hfork
  have hclearRun : (clearState s source rest).halt = .Running := by
    simpa [clearState, PackedCompressionGapSite.gapCleared] using hrun
  have hclearNp : Precompile.isPrecompileWithConfig
      (clearState s source rest).executionEnv.precompileConfig
      (clearState s source rest).executionEnv.fork
      (clearState s source rest).executionEnv.codeAddr = false := by
    simpa [clearState, PackedCompressionGapSite.gapCleared] using hnp
  have hswapRaw := PackedPreprocessByteSwap.gasSteps_byteSwap
    (clearState s source rest)
    source rest hsource hnowrap hstack hartifactCode hclearFork hclearRun hclearNp
  have hswap : GasSteps (clearState s source rest)
      (swappedState s source rest) :=
    hswapRaw.cast (clearState_eq_byteSwapEntry s source rest).symm rfl
  have hactive : 11 ≤ (swappedState s source rest).activeWords.toNat := by
    simpa [swappedState] using
      PackedPreprocessByteSwap.loadedActiveWords_ge_11
        (clearState s source rest) source
        hsource hnowrap
  have hswappedCode :
      (swappedState s source rest).executionEnv.code = submissionBytecode := by
    simpa [swappedState, clearState,
      PackedCompressionGapSite.gapCleared] using hcode
  have hswappedFork : (swappedState s source rest).fork = .Osaka := by
    change (swappedState s source rest).executionEnv.fork = .Osaka
    rw [show (swappedState s source rest).executionEnv = s.executionEnv by
      simp [swappedState, clearState,
        PackedCompressionGapSite.gapCleared]]
    exact hfork
  have hswappedRun : (swappedState s source rest).halt = .Running := by
    simpa [swappedState, clearState,
      PackedCompressionGapSite.gapCleared] using hrun
  have hswappedNp : Precompile.isPrecompileWithConfig
      (swappedState s source rest).executionEnv.precompileConfig
      (swappedState s source rest).executionEnv.fork
      (swappedState s source rest).executionEnv.codeAddr = false := by
    simpa [swappedState, clearState,
      PackedCompressionGapSite.gapCleared] using hnp
  have hspreadRaw := PackedPreprocessSpreadSite.gasSteps_spread
    (swappedState s source rest) rest
    hactive (by omega) hswappedCode hswappedFork hswappedRun hswappedNp
  have hspread : GasSteps (swappedState s source rest)
      (preprocessReturned s source rest) :=
    hspreadRaw.cast (swappedState_eq_spreadEntry s source rest).symm rfl
  exact hgap.trans (hswap.trans hspread)

#print axioms clearState_readWord_above
#print axioms spreadValue_eq_expected
#print axioms preprocessReturned_gap
#print axioms preprocessReturned_read_above
#print axioms preprocessReturned_activeWords_ge_18
#print axioms gasSteps_preprocess

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessTrace
