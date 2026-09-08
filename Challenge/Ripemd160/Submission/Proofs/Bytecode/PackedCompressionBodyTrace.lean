import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPreprocessTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedHashEntryTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedLocatedFullRoundsActiveWords
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionEndpoint

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

/-!
# Located packed compression body

This is the concrete composition from the first gap-clearing instruction at
PC `539`, through byte-swap and spread preprocessing, the hash-entry frame,
and all eighty packed rounds.  It stops at PC `5066`, immediately before the
combine tail.

The source loads in preprocessing establish the active-memory lower bound
used by hash entry and retained for the combine stores.  No active-memory
premise is added to the caller-facing theorem.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionBodyTrace

open Challenge.Ripemd160 Challenge.EvmProof
open EvmSemantics EvmSemantics.EVM
open PackedStepFrame PackedRoundSequence PackedRunOpBridge

/-- The scratch memory immediately before the sixteen descending spread
stores. -/
def baseMemory (s : State) (source : Nat) (ret xoff xend : UInt256)
    (rest : List UInt256) : ByteArray :=
  (PackedPreprocessTrace.swappedState s source
    ([ret, xoff, xend] ++ rest)).memory

/-- The sixteen words physically selected by preprocessing. -/
def messageWords (s : State) (source : Nat) (ret xoff xend : UInt256)
    (rest : List UInt256) (i : Nat) : UInt256 :=
  PackedPreprocessLayout.spreadValue
    (baseMemory s source ret xoff xend rest) i

/-- The mathematical frame reached by the located eighty-round trace. -/
def endpoint (s : State) (source : Nat) (h : Compression.HashState)
    (ret xoff xend : UInt256) (rest : List UInt256) : PackedStepFrame.Frame :=
  PackedCompressionEndpoint.endpoint
    (baseMemory s source ret xoff xend rest)
    (messageWords s source ret xoff xend rest) h ret xoff xend

theorem baseMemory_gap (s : State) (source : Nat)
    (ret xoff xend : UInt256) (rest : List UInt256) :
    PackedGapInvariant.GapZero
      (baseMemory s source ret xoff xend rest) := by
  apply PackedPreprocessPreservation.packedBaseMemory_gap
  exact PackedCompressionGapSite.gapCleared_gapZero s
    (UInt256.ofNat source :: [ret, xoff, xend] ++ rest)

/-- The endpoint's message reader is the original input reader, not the
byte-swapped scratch representation. -/
theorem messageWords_eq_expected (s : State) (source : Nat)
    (ret xoff xend : UInt256) (rest : List UInt256)
    (hsource : 512 ≤ source) (hnowrap : source + 64 < 2 ^ 256)
    (i : Nat) (hi : i < 16) :
    messageWords s source ret xoff xend rest i =
      ScheduleCorrect.expectedWord s.memory
        (PackedScheduleMemory.naturalp source) i := by
  exact PackedPreprocessTrace.spreadValue_eq_expected s source i
    ([ret, xoff, xend] ++ rest) hsource hi hnowrap

/-- Arithmetic endpoint specialization exposed for the subsequent combine
trace. -/
theorem endpoint_result (s : State) (source : Nat)
    (h : Compression.HashState) (ret xoff xend : UInt256)
    (rest : List UInt256) (values : Nat → UInt32)
    (hsource : 512 ≤ source) (hnowrap : source + 64 < 2 ^ 256)
    (hvalues : ∀ i, i < 16 →
      (ScheduleCorrect.expectedWord s.memory
        (PackedScheduleMemory.naturalp source) i).toNat =
          (values i).toNat) :
    PackedCombine.packedCombine (Compression.embedHash h)
      (endpoint s source h ret xoff xend rest).regs =
        Compression.embedHash (CompressionCorrect.compressModel values h) := by
  apply PackedCompressionEndpoint.endpoint_result
    (baseMemory s source ret xoff xend rest)
    (messageWords s source ret xoff xend rest) values
    (baseMemory_gap s source ret xoff xend rest)
  intro i hi
  rw [messageWords_eq_expected s source ret xoff xend rest
    hsource hnowrap i hi]
  exact hvalues i hi

theorem round79_endPC :
    (PackedRoundSites.roundSite (79 : Fin 80)).endPC =
      UInt256.ofNat 5066 := by
  rfl

/-- Exact located execution from preprocessing entry through round 79.

The only semantic inputs are the original chaining words in memory, the
source range, and the ordinary machine/code conditions.  In particular,
the active-memory lower bound is derived from the two source `MLOAD`s. -/
theorem gasSteps_body (s : State) (source : Nat)
    (h : Compression.HashState) (ret xoff xend : UInt256)
    (rest : List UInt256)
    (hsource : 512 ≤ source) (hnowrap : source + 64 < 2 ^ 256)
    (hhash : StackMemory.hashAt s.memory = Compression.embedHash h)
    (hrest : rest.length + 72 < 1024)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    ∃ t, ∃ _trace : GasSteps
        (PackedPreprocessTrace.preprocessEntry s source
          ([ret, xoff, xend] ++ rest)) t,
      t.stack = frameStack (endpoint s source h ret xoff xend rest) ++ rest ∧
      t.memory = (PackedPreprocessTrace.preprocessReturned s source
        ([ret, xoff, xend] ++ rest)).memory ∧
      t.executionEnv = s.executionEnv ∧
      t.halt = .Running ∧
      t.callStack = s.callStack ∧
      t.pc = UInt256.ofNat 5066 ∧
      16 ≤ t.activeWords.toNat := by
  let suffix : List UInt256 := [ret, xoff, xend] ++ rest
  let preprocessed : State :=
    PackedPreprocessTrace.preprocessReturned s source suffix
  let entered : State := PackedHashEntryTrace.frameReturned preprocessed
    PackedHashEntryTrace.hashEntrySite.endPC h ret xoff xend rest
  have hpreprocess : GasSteps
      (PackedPreprocessTrace.preprocessEntry s source suffix) preprocessed := by
    exact PackedPreprocessTrace.gasSteps_preprocess s source suffix
      hsource hnowrap (by simp [suffix]; omega) hcode hfork hrun hnp
  have hpreActive : 16 ≤ preprocessed.activeWords.toNat := by
    have h18 := PackedPreprocessTrace.preprocessReturned_activeWords_ge_18
      s source suffix hsource hnowrap
    have h16 : 16 ≤ (PackedPreprocessTrace.preprocessReturned s source
        suffix).activeWords.toNat := (by omega : 16 ≤ 18).trans h18
    simpa [preprocessed] using h16
  have hpreHash :
      StackMemory.hashAt preprocessed.memory = Compression.embedHash h := by
    have h352 := PackedPreprocessTrace.preprocessReturned_read_above
      s source suffix 352 (by omega)
    have h384 := PackedPreprocessTrace.preprocessReturned_read_above
      s source suffix 384 (by omega)
    have h416 := PackedPreprocessTrace.preprocessReturned_read_above
      s source suffix 416 (by omega)
    have h448 := PackedPreprocessTrace.preprocessReturned_read_above
      s source suffix 448 (by omega)
    have h480 := PackedPreprocessTrace.preprocessReturned_read_above
      s source suffix 480 (by omega)
    unfold StackMemory.hashAt at hhash ⊢
    rw [show MachineState.readWord preprocessed.memory 352 =
        MachineState.readWord s.memory 352 by simpa [preprocessed] using h352,
      show MachineState.readWord preprocessed.memory 384 =
        MachineState.readWord s.memory 384 by simpa [preprocessed] using h384,
      show MachineState.readWord preprocessed.memory 416 =
        MachineState.readWord s.memory 416 by simpa [preprocessed] using h416,
      show MachineState.readWord preprocessed.memory 448 =
        MachineState.readWord s.memory 448 by simpa [preprocessed] using h448,
      show MachineState.readWord preprocessed.memory 480 =
        MachineState.readWord s.memory 480 by simpa [preprocessed] using h480]
    exact hhash
  have hpreEnv : preprocessed.executionEnv = s.executionEnv := by
    change (PackedPreprocessTrace.preprocessReturned s source
      suffix).executionEnv = s.executionEnv
    exact PackedPreprocessTrace.preprocessReturned_executionEnv s source suffix
  have hpreCode : preprocessed.executionEnv.code = submissionBytecode := by
    rw [hpreEnv]
    exact hcode
  have hpreFork : preprocessed.fork = .Osaka := by
    change preprocessed.executionEnv.fork = .Osaka
    rw [hpreEnv]
    exact hfork
  have hpreRun : preprocessed.halt = .Running := by
    rw [show preprocessed.halt = s.halt by
      change (PackedPreprocessTrace.preprocessReturned s source suffix).halt =
        s.halt
      exact PackedPreprocessTrace.preprocessReturned_halt s source suffix]
    exact hrun
  have hpreNp : Precompile.isPrecompileWithConfig
      preprocessed.executionEnv.precompileConfig preprocessed.executionEnv.fork
      preprocessed.executionEnv.codeAddr = false := by
    rw [hpreEnv]
    exact hnp
  have hentryRaw := PackedHashEntryTrace.gasSteps_hashEntry preprocessed h
    ret xoff xend rest hpreHash hpreActive (by omega) hpreCode hpreFork
    hpreRun hpreNp
  have hentryStart : PackedHashEntryTrace.entryState preprocessed
      PackedHashEntryTrace.hashEntrySite.startPC ret xoff xend rest =
        preprocessed := by
    have hpc : PackedHashEntryTrace.hashEntrySite.startPC = preprocessed.pc := by
      rw [PackedHashEntryTrace.hashEntrySite_startPC]
      symm
      change (PackedPreprocessTrace.preprocessReturned s source suffix).pc =
        UInt256.ofNat 784
      exact PackedPreprocessTrace.preprocessReturned_pc s source suffix
    have hstack : [ret, xoff, xend] ++ rest = preprocessed.stack := by
      symm
      change (PackedPreprocessTrace.preprocessReturned s source suffix).stack =
        [ret, xoff, xend] ++ rest
      rw [PackedPreprocessTrace.preprocessReturned_stack]
    unfold PackedHashEntryTrace.entryState
    rw [hpc, hstack]
  have hentry : GasSteps preprocessed entered :=
    hentryRaw.cast hentryStart rfl
  have henteredStart : PathStarts
      (PackedRoundSites.roundSite (0 : Fin 80)).path entered := by
    apply PackedLocatedRoundChain.pathStarts_of_statePC_eq_start
    change PackedHashEntryTrace.hashEntrySite.endPC =
      (PackedRoundSites.roundSite (0 : Fin 80)).startPC
    rw [PackedHashEntryTrace.hashEntrySite_endPC]
    rfl
  have henteredEnv : entered.executionEnv = s.executionEnv := by
    exact (show entered.executionEnv = preprocessed.executionEnv by rfl).trans
      hpreEnv
  have henteredCode : entered.executionEnv.code = Artifact.submissionArtifact.code := by
    change entered.executionEnv.code = submissionBytecode
    rw [henteredEnv]
    exact hcode
  have henteredFork : entered.fork = .Osaka := by
    change entered.executionEnv.fork = .Osaka
    rw [henteredEnv]
    exact hfork
  have henteredRun : entered.halt = .Running := by
    change preprocessed.halt = .Running
    exact hpreRun
  have henteredNp : Precompile.isPrecompileWithConfig
      entered.executionEnv.precompileConfig entered.executionEnv.fork
      entered.executionEnv.codeAddr = false := by
    rw [henteredEnv]
    exact hnp
  have henteredActive : 16 ≤ entered.activeWords.toNat := by
    simpa [entered, PackedHashEntryTrace.frameReturned] using hpreActive
  obtain ⟨t, roundsTrace, htstack, htmemory, htenv, hthalt, htcalls,
      htpc, htactive⟩ :=
    PackedLocatedFullRoundsActiveWords.full_rounds_activeWords_ge 16 entered
      (PackedInitialFrame.initialFrame h ret xoff xend) rest henteredActive
      (by simp [entered, PackedHashEntryTrace.frameReturned])
      (PackedInitialFrame.initialFrame_phase h ret xoff xend)
      (PackedInitialFrame.initialFrame_ready h ret xoff xend)
      hrest henteredStart henteredCode henteredFork henteredRun henteredNp
  have hmemoryWord : memoryWord entered = PackedMemoryOperands.reader
      (PackedGapInvariant.spreadWords
        (messageWords s source ret xoff xend rest) 16
        (baseMemory s source ret xoff xend rest)) := by
    have henteredMemory : entered.memory = preprocessed.memory := rfl
    have hpreprocessedMemory : preprocessed.memory =
        PackedPreprocessLayout.spreadMemory
          (baseMemory s source ret xoff xend rest) := by
      change (PackedPreprocessTrace.preprocessReturned s source suffix).memory =
        PackedPreprocessLayout.spreadMemory
          (PackedPreprocessTrace.swappedState s source suffix).memory
      rw [PackedPreprocessTrace.preprocessReturned_memory]
      rfl
    funext address
    unfold memoryWord PackedMemoryOperands.reader
    rw [henteredMemory, hpreprocessedMemory]
    rfl
  rw [hmemoryWord] at htstack
  refine ⟨t, hpreprocess.trans (hentry.trans roundsTrace), ?_,
    htmemory.trans ?_, htenv.trans ?_, hthalt, htcalls.trans ?_,
    htpc.trans round79_endPC, htactive⟩
  · simpa [endpoint, PackedCompressionEndpoint.endpoint] using htstack
  · rfl
  · exact henteredEnv
  · exact (show entered.callStack = preprocessed.callStack by rfl).trans (by
      change (PackedPreprocessTrace.preprocessReturned s source
        suffix).callStack = s.callStack
      exact PackedPreprocessTrace.preprocessReturned_callStack s source suffix)

#print axioms baseMemory_gap
#print axioms messageWords_eq_expected
#print axioms endpoint_result
#print axioms round79_endPC
#print axioms gasSteps_body

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompressionBodyTrace
