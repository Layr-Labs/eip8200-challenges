import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionModel
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionFunctionalTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.CompressionSeamBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputResultBridge
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddedBlockBridge

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

/-!
# Conditional iterated RIPEMD-160 compression run

This layer carries the executable compressor's pure state and functional hash
invariant across the padded blocks.  The per-block machine trace is an
explicit restricted witness: the immediate-wrapper worker can provide it
without importing the obsolete full-trace gas theorem.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateRunTrace

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM
open CompressionTrace
open CompressionFunctionalTrace

def states (input : ByteArray) : Nat → State
  | 0 => PaddingTrace.padReturned input
  | n + 1 => CompressionModel.resultState (states input n) input n

@[simp] theorem states_executionEnv (input : ByteArray) (n : Nat) :
    (states input n).executionEnv =
      (PaddingTrace.padReturned input).executionEnv := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [states] using ih

@[simp] theorem states_halt (input : ByteArray) (n : Nat) :
    (states input n).halt = .Running := by
  induction n with
  | zero => exact PaddingTrace.padReturned_halt input
  | succ n ih => simpa [states] using ih

@[simp] theorem states_callStack (input : ByteArray) (n : Nat) :
    (states input n).callStack = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [states] using ih

def initialHashState : Compression.HashState :=
  { h0 := Crypto.Ripemd160.H0[0]!
    h1 := Crypto.Ripemd160.H0[1]!
    h2 := Crypto.Ripemd160.H0[2]!
    h3 := Crypto.Ripemd160.H0[3]!
    h4 := Crypto.Ripemd160.H0[4]! }

def hashStateAfter (input : ByteArray) : Nat → Compression.HashState
  | 0 => initialHashState
  | n + 1 => CompressionCorrect.compressModel
      (blockWords (Padding.paddedMessage input) (n * 64))
      (hashStateAfter input n)

theorem hashAfter_succ (input : ByteArray) (n : Nat) :
    CompressionSeamBridge.hashAfter input (n + 1) =
      Crypto.Ripemd160.compressBlock
        (CompressionSeamBridge.hashAfter input n)
        (Padding.paddedMessage input) (n * 64) := by
  unfold CompressionSeamBridge.hashAfter
  simpa using SpecBridge.absorbBlocks_succ Crypto.Ripemd160.H0
    (Padding.paddedMessage input) 0 n

theorem hashArray_hashStateAfter (input : ByteArray) (n : Nat) :
    CompressionCorrect.hashArray (hashStateAfter input n) =
      CompressionSeamBridge.hashAfter input n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [hashStateAfter, hashAfter_succ,
        compressModel_hashArray_eq_compressBlock, ih]

private theorem padReturned_word_below (input : ByteArray)
    (hfit : CalldataFits input) (address : Nat)
    (haddress : address + 32 ≤ Padding.messageOffset) :
    wordAt (PaddingTrace.padReturned input) address =
      wordAt (Main.initializedState input) address := by
  unfold wordAt
  rw [PaddingTrace.padReturned_memory input hfit]
  unfold Padding.paddedMemory Padding.sentinelMemory Padding.copiedMemory
  have hpadded := Padding.input_and_footer_fit input.size
  rw [Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint,
    Challenge.EvmProof.Memory.readWord_writeBytes_disjoint]
  · rfl
  all_goals
    left
    simp [Padding.messageOffset] at haddress ⊢
    omega

private theorem initialTables (input : ByteArray) (hfit : CalldataFits input) :
    InitializationCorrect.TablesCorrect
      (PaddingTrace.padReturned input).memory := by
  rcases InitializationCorrect.initializedState_tables input with
    ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x4a0 + 32 * (i / 32)) =
        MachineState.readWord (Main.initializedState input).memory
          (0x4a0 + 32 * (i / 32)) by
      exact padReturned_word_below input hfit _ (by
        simp [Padding.messageOffset]
        omega)]
    exact hr i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x500 + 32 * (i / 32)) =
        MachineState.readWord (Main.initializedState input).memory
          (0x500 + 32 * (i / 32)) by
      exact padReturned_word_below input hfit _ (by
        simp [Padding.messageOffset]
        omega)]
    exact hrP i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x560 + 32 * (i / 32)) =
        MachineState.readWord (Main.initializedState input).memory
          (0x560 + 32 * (i / 32)) by
      exact padReturned_word_below input hfit _ (by
        simp [Padding.messageOffset]
        omega)]
    exact hs i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x5c0 + 32 * (i / 32)) =
        MachineState.readWord (Main.initializedState input).memory
          (0x5c0 + 32 * (i / 32)) by
      exact padReturned_word_below input hfit _ (by
        simp [Padding.messageOffset]
        omega)]
    exact hsP i hi

def ConstantsCorrect (s : State) : Prop :=
  (∀ j, j < 5 →
      InitializationCorrect.slotWord s.memory 0x620 j =
        Word.ofUInt32 (Crypto.Ripemd160.K[j]!)) ∧
  (∀ j, j < 5 →
      InitializationCorrect.slotWord s.memory 0x6c0 j =
        Word.ofUInt32 (Crypto.Ripemd160.KP[j]!))

private theorem initialConstants (input : ByteArray)
    (hfit : CalldataFits input) :
    ConstantsCorrect (PaddingTrace.padReturned input) := by
  unfold ConstantsCorrect
  rcases InitializationCorrect.initializedState_constants input with
    ⟨hk, hkP, _⟩
  constructor
  · intro j hj
    unfold InitializationCorrect.slotWord
    rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x620 + 32 * j) =
        MachineState.readWord (Main.initializedState input).memory
          (0x620 + 32 * j) by
      exact padReturned_word_below input hfit _ (by
        simp [Padding.messageOffset]
        omega)]
    exact hk j hj
  · intro j hj
    unfold InitializationCorrect.slotWord
    rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x6c0 + 32 * j) =
        MachineState.readWord (Main.initializedState input).memory
          (0x6c0 + 32 * j) by
      exact padReturned_word_below input hfit _ (by
        simp [Padding.messageOffset]
        omega)]
    exact hkP j hj

theorem states_word_above (input : ByteArray) (n address : Nat)
    (haddress : 0x4a0 ≤ address) :
    wordAt (states input n) address =
      wordAt (PaddingTrace.padReturned input) address := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [states]
      change wordAt
          (CompressionTailTrace.rightTailResult
            (leftFinalState (states input n) (DriverTrace.messageOffsetWord n)
              (UInt256.ofNat 0x643) (CompressionModel.driverRest input n))
            (DriverTrace.messageOffsetWord n) (UInt256.ofNat 0x643)
            (CompressionModel.driverRest input n)) address = _
      rw [compressorResult_word_above _ _ _ _ address haddress, ih]

theorem statesTables (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) : InitializationCorrect.TablesCorrect (states input n).memory := by
  rcases initialTables input hfit with ⟨hr, hrP, hs, hsP⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (states input n).memory
          (0x4a0 + 32 * (i / 32)) =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x4a0 + 32 * (i / 32)) by
      exact states_word_above input n _ (by omega)]
    exact hr i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (states input n).memory
          (0x500 + 32 * (i / 32)) =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x500 + 32 * (i / 32)) by
      exact states_word_above input n _ (by omega)]
    exact hrP i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (states input n).memory
          (0x560 + 32 * (i / 32)) =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x560 + 32 * (i / 32)) by
      exact states_word_above input n _ (by omega)]
    exact hs i hi
  · intro i hi
    unfold InitializationCorrect.tableByte
    rw [show MachineState.readWord (states input n).memory
          (0x5c0 + 32 * (i / 32)) =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x5c0 + 32 * (i / 32)) by
      exact states_word_above input n _ (by omega)]
    exact hsP i hi

theorem statesConstants (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) : ConstantsCorrect (states input n) := by
  unfold ConstantsCorrect
  rcases initialConstants input hfit with ⟨hk, hkP⟩
  constructor
  · intro j hj
    unfold InitializationCorrect.slotWord
    rw [show MachineState.readWord (states input n).memory (0x620 + 32 * j) =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x620 + 32 * j) by
      exact states_word_above input n _ (by omega)]
    exact hk j hj
  · intro j hj
    unfold InitializationCorrect.slotWord
    rw [show MachineState.readWord (states input n).memory (0x6c0 + 32 * j) =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (0x6c0 + 32 * j) by
      exact states_word_above input n _ (by omega)]
    exact hkP j hj

private theorem statesMessageBlock (input : ByteArray)
    (hfit : CalldataFits input) (n : Nat)
    (hn : n < DriverTrace.blockCount input) :
    ScheduleCorrect.MessageBlockAt (states input n).memory
      (DriverTrace.messageOffsetWord n) (Padding.paddedMessage input)
      (DriverTrace.blockOffset n) := by
  have hbase := DriverTrace.padReturned_messageBlockAt input hfit n hn
  intro k hk
  unfold ScheduleCorrect.expectedWord Schedule.readLEWord
  rw [show MachineState.readWord (states input n).memory
          (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord n) k).toNat =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord n) k).toNat by
    exact states_word_above input n _
      (DriverTrace.padReturned_blockSeparated input hfit n hn k hk)]
  exact hbase k hk

private theorem hashAt32_of_hashWords
    (hw : CompressionSeamBridge.HashWordsAt input n s) :
    hashAt32 s = Compression.embedHash (hashStateAfter input n) := by
  unfold hashAt32 Compression.embedHash
  rw [show wordAt s 32 = OutputTrace.hWord s 0 by rfl,
    show wordAt s 64 = OutputTrace.hWord s 1 by rfl,
    show wordAt s 96 = OutputTrace.hWord s 2 by rfl,
    show wordAt s 128 = OutputTrace.hWord s 3 by rfl,
    show wordAt s 160 = OutputTrace.hWord s 4 by rfl,
    hw ⟨0, by omega⟩, hw ⟨1, by omega⟩, hw ⟨2, by omega⟩,
    hw ⟨3, by omega⟩, hw ⟨4, by omega⟩]
  rw [← hashArray_hashStateAfter input n]
  rfl

private theorem initialHashWords (input : ByteArray) (hfit : CalldataFits input) :
    CompressionSeamBridge.HashWordsAt input 0 (states input 0) := by
  intro i
  change OutputTrace.hWord (PaddingTrace.padReturned input) i = _
  have hh := (InitializationCorrect.initializedState_constants input).2.2
    i i.isLt
  unfold OutputTrace.hWord
  rw [show MachineState.readWord (PaddingTrace.padReturned input).memory
        (OutputTrace.hOffset i) =
      MachineState.readWord (Main.initializedState input).memory
        (OutputTrace.hOffset i) by
    exact padReturned_word_below input hfit _ (by
      unfold OutputTrace.hOffset Padding.messageOffset
      omega)]
  simpa [CompressionSeamBridge.hashAfter, SpecBridge.absorbBlocks,
    OutputTrace.hOffset, InitializationCorrect.slotWord, Nat.mul_comm] using hh

private theorem hashWords_succ (input : ByteArray) (hfit : CalldataFits input)
    (n : Nat) (hn : n < DriverTrace.blockCount input)
    (hw : CompressionSeamBridge.HashWordsAt input n (states input n)) :
    CompressionSeamBridge.HashWordsAt input (n + 1) (states input (n + 1)) := by
  let h := hashStateAfter input n
  have hinputs : BlockInputs (states input n)
      (DriverTrace.messageOffsetWord n) (Padding.paddedMessage input)
      (DriverTrace.blockOffset n) h := {
    separated := DriverTrace.padReturned_blockSeparated input hfit n hn
    messageBlock := statesMessageBlock input hfit n hn
    tables := statesTables input hfit n
    constants := statesConstants input hfit n
    hash := hashAt32_of_hashWords hw }
  have hout := tail_hash_eq_compressBlock_of_inputs
    (returnDest := UInt256.ofNat 0x643)
    (rest := CompressionModel.driverRest input n) hinputs
  have harray := hashArray_hashStateAfter input n
  rw [harray] at hout
  rw [states]
  intro i
  rw [hashAfter_succ]
  change OutputTrace.hWord
      (CompressionTailTrace.rightTailResult
        (leftFinalState (states input n) (DriverTrace.messageOffsetWord n)
          (UInt256.ofNat 0x643) (CompressionModel.driverRest input n))
        (DriverTrace.messageOffsetWord n) (UInt256.ofNat 0x643)
        (CompressionModel.driverRest input n)) i = _
  fin_cases i
  · exact congrArg Compression.EvmHashState.h0 hout
  · exact congrArg Compression.EvmHashState.h1 hout
  · exact congrArg Compression.EvmHashState.h2 hout
  · exact congrArg Compression.EvmHashState.h3 hout
  · exact congrArg Compression.EvmHashState.h4 hout

theorem hashWords (input : ByteArray) (hfit : CalldataFits input) :
    ∀ n, n ≤ DriverTrace.blockCount input →
      CompressionSeamBridge.HashWordsAt input n (states input n) := by
  intro n hn
  induction n with
  | zero => exact initialHashWords input hfit
  | succ n ih => exact hashWords_succ input hfit n (by omega) (ih (by omega))

def RestrictedBlockTrace (s : State) (input : ByteArray) (i : Nat)
    (_hfit : CalldataFits input) : Type :=
  ∀ (_hi : i < DriverTrace.blockCount input)
    (_htables : InitializationCorrect.TablesCorrect s.memory)
    (_hconstants : ConstantsCorrect s)
    (_hcode : s.executionEnv.code = submissionBytecode)
    (_hfork : s.fork = .Osaka)
    (_hrun : s.halt = .Running)
    (_hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false),
    GasSteps (DriverTrace.compressEntry s input i)
      (DriverTrace.compressReturned
        (CompressionModel.resultState s input i) input i)

noncomputable def compressionRun (input : ByteArray) (hfit : CalldataFits input)
    (hstep : ∀ i, RestrictedBlockTrace (states input i) input i hfit) :
    CompressionSeamBridge.CompressionRun input where
  states := states input
  initial := by
    let s := PaddingTrace.padReturned input
    have hpc : s.pc = UInt256.ofNat 0x62c := PaddingTrace.padReturned_pc input
    have hstack : s.stack = [Padding.paddedWord input] :=
      PaddingTrace.padReturned_stack input
    change DriverTrace.setupEntry s input = s
    unfold DriverTrace.setupEntry
    rw [← hpc, ← hstack]
  code := by
    intro i hi
    rw [states_executionEnv]
    exact PaddingTrace.padReturned_code input
  fork := by
    intro i hi
    rw [State.fork, states_executionEnv]
    exact PaddingTrace.padReturned_fork input
  running := fun i _ => states_halt input i
  noPrecompile := by
    intro i hi
    rw [states_executionEnv]
    exact PaddingTrace.padReturned_noPrecompile input
  callStack := fun i _ => states_callStack input i
  blockTrace := by
    intro i hi
    exact hstep i hi (statesTables input hfit i)
      (statesConstants input hfit i)
      (by rw [states_executionEnv]; exact PaddingTrace.padReturned_code input)
      (by
        rw [State.fork, states_executionEnv]
        exact PaddingTrace.padReturned_fork input)
      (states_halt input i)
      (by
        rw [states_executionEnv]
        exact PaddingTrace.padReturned_noPrecompile input)
  hashWords := hashWords input hfit

/-- A uniform restricted block witness yields a run for every fitting input.
This remains a conditional interface until the immediate compressor worker
supplies that witness. -/
noncomputable def compressionRun_all
    (hstep : ∀ (input : ByteArray) (hfit : CalldataFits input) (i : Nat),
      RestrictedBlockTrace (states input i) input i hfit) :
    ∀ input : ByteArray, CalldataFits input →
      CompressionSeamBridge.CompressionRun input := by
  intro input hfit
  exact compressionRun input hfit (hstep input hfit)

/-- Conditional final correctness from the restricted immediate compressor
witness. -/
theorem correct_of_restrictedBlockTrace
    (hstep : ∀ (input : ByteArray) (hfit : CalldataFits input) (i : Nat),
      RestrictedBlockTrace (states input i) input i hfit) :
    Correct submissionBytecode :=
  OutputResultBridge.correct_of_compression_trace
    (fun input hfit =>
      CompressionSeamBridge.toCompressionSeam
        (compressionRun input hfit (hstep input hfit)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ImmediateRunTrace
