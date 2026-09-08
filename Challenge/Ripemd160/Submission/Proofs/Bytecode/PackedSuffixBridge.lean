import Challenge.Ripemd160.Submission.Proofs.Bytecode.StackRunBridge

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-!
# Seeded suffix execution for the packed RIPEMD-160 block kernel

The ordinary `StackRunBridge.states` family starts at padded block zero with
the initial RIPEMD chaining words.  A sound first-block fast path instead
reaches the driver's post-check with the chaining words for block one already
installed.  This file supplies the missing generic bridge: run the unchanged
block kernel over the global interval `start .. blockCount input` from an
arbitrary certified seed.

The state family is indexed by an offset `k`, but every kernel call and hash
invariant uses the global block number `start + k`.  Message memory is related
back to `PaddingTrace.padReturned` only at addresses at or above `0x200`, which
is exactly the region from which the block scheduler reads.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSuffixBridge

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

namespace SRB

abbrev wordAt := StackRunBridge.wordAt
abbrev hashAt32 := StackRunBridge.hashAt32
abbrev embedHashArray := StackRunBridge.embedHashArray
abbrev BlockContext := StackRunBridge.BlockContext
abbrev BlockKernel := StackRunBridge.BlockKernel
abbrev hashStateAfter := StackRunBridge.hashStateAfter

end SRB

namespace CSB

abbrev HashWordsAt := CompressionSeamBridge.HashWordsAt
abbrev hashAfter := CompressionSeamBridge.hashAfter

end CSB

/-- Facts required of a state that is about to enter the driver loop at the
global block index `start`. -/
structure SeedInvariant (input : ByteArray) (start : Nat) (seed : State) : Prop where
  calldata : seed.executionEnv.calldata = input
  code : seed.executionEnv.code = submissionBytecode
  fork : seed.fork = .Osaka
  running : seed.halt = .Running
  noPrecompile : Precompile.isPrecompileWithConfig seed.executionEnv.precompileConfig
    seed.executionEnv.fork seed.executionEnv.codeAddr = false
  callStack : seed.callStack = []
  wordAbovePad : ∀ address, 0x200 ≤ address →
    SRB.wordAt seed address = SRB.wordAt (PaddingTrace.padReturned input) address
  hashWords : CSB.HashWordsAt input start seed

/-- The `k`th state of a suffix run.  Its next transition always uses the
global block index `start + k`, never a zero-based replacement index. -/
def statesFrom (kernel : SRB.BlockKernel) (input : ByteArray) (start : Nat)
    (seed : State) : Nat → State
  | 0 => seed
  | k + 1 => kernel.nextState (statesFrom kernel input start seed k) input (start + k)

@[simp] theorem statesFrom_zero (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) :
    statesFrom kernel input start seed 0 = seed := by
  rfl

@[simp] theorem statesFrom_succ (kernel : SRB.BlockKernel) (input : ByteArray)
    (start k : Nat) (seed : State) :
    statesFrom kernel input start seed (k + 1) =
      kernel.nextState (statesFrom kernel input start seed k) input (start + k) := by
  rfl

theorem statesFrom_executionEnv (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (k : Nat) :
    (statesFrom kernel input start seed k).executionEnv = seed.executionEnv := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [statesFrom, StackRunBridge.BlockKernel.executionEnv, ih]

theorem statesFrom_halt (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (k : Nat) :
    (statesFrom kernel input start seed k).halt = seed.halt := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [statesFrom, StackRunBridge.BlockKernel.halt, ih]

theorem statesFrom_callStack (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (k : Nat) :
    (statesFrom kernel input start seed k).callStack = seed.callStack := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [statesFrom, StackRunBridge.BlockKernel.callStack, ih]

theorem statesFrom_wordAbove_seed (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (k address : Nat) (haddress : 0x200 ≤ address) :
    SRB.wordAt (statesFrom kernel input start seed k) address =
      SRB.wordAt seed address := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [statesFrom]
      exact (StackRunBridge.BlockKernel.wordAbove kernel
        (statesFrom kernel input start seed k) input (start + k) address haddress).trans ih

theorem statesFrom_wordAbove_pad (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed)
    (k address : Nat) (haddress : 0x200 ≤ address) :
    SRB.wordAt (statesFrom kernel input start seed k) address =
      SRB.wordAt (PaddingTrace.padReturned input) address :=
  (statesFrom_wordAbove_seed kernel input start seed k address haddress).trans
    (inv.wordAbovePad address haddress)

theorem statesFrom_calldata (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed) (k : Nat) :
    (statesFrom kernel input start seed k).executionEnv.calldata = input := by
  rw [statesFrom_executionEnv]
  exact inv.calldata

theorem statesFrom_code (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed) (k : Nat) :
    (statesFrom kernel input start seed k).executionEnv.code = submissionBytecode := by
  rw [statesFrom_executionEnv]
  exact inv.code

theorem statesFrom_fork (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed) (k : Nat) :
    (statesFrom kernel input start seed k).fork = .Osaka := by
  change (statesFrom kernel input start seed k).executionEnv.fork = .Osaka
  rw [statesFrom_executionEnv]
  exact inv.fork

theorem statesFrom_running (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed) (k : Nat) :
    (statesFrom kernel input start seed k).halt = .Running := by
  rw [statesFrom_halt]
  exact inv.running

theorem statesFrom_noPrecompile (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed) (k : Nat) :
    Precompile.isPrecompileWithConfig
      (statesFrom kernel input start seed k).executionEnv.precompileConfig
      (statesFrom kernel input start seed k).executionEnv.fork
      (statesFrom kernel input start seed k).executionEnv.codeAddr = false := by
  rw [statesFrom_executionEnv]
  exact inv.noPrecompile

theorem statesFrom_callStack_nil (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed) (k : Nat) :
    (statesFrom kernel input start seed k).callStack = [] := by
  rw [statesFrom_callStack]
  exact inv.callStack

private theorem blockSeparated (input : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i < DriverTrace.blockCount input) :
    ∀ k, k < 16 →
      0x200 ≤ (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord i) k).toNat := by
  simpa [DriverTrace.messageOffsetWord, DriverTrace.blockOffset,
    DriverTrace.blockCount] using
    PaddedBlockBridge.padReturned_blockIndexSeparated input hfit i (by
      simpa [DriverTrace.blockCount] using hi)

private theorem messageBlockAt (kernel : SRB.BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (start : Nat) (seed : State)
    (inv : SeedInvariant input start seed) (k : Nat)
    (hk : start + k < DriverTrace.blockCount input) :
    ScheduleCorrect.MessageBlockAt (statesFrom kernel input start seed k).memory
      (DriverTrace.messageOffsetWord (start + k)) (Padding.paddedMessage input)
      (DriverTrace.blockOffset (start + k)) := by
  have hbase : ScheduleCorrect.MessageBlockAt
      (PaddingTrace.padReturned input).memory
      (DriverTrace.messageOffsetWord (start + k)) (Padding.paddedMessage input)
      (DriverTrace.blockOffset (start + k)) := by
    simpa [DriverTrace.messageOffsetWord, DriverTrace.blockOffset,
      DriverTrace.blockCount] using
      PaddedBlockBridge.padReturned_blockIndexAt input hfit (start + k) (by
        simpa [DriverTrace.blockCount] using hk)
  have hsep := blockSeparated input hfit (start + k) hk
  intro j hj
  unfold ScheduleCorrect.expectedWord Schedule.readLEWord
  rw [show MachineState.readWord (statesFrom kernel input start seed k).memory
          (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord (start + k)) j).toNat =
        MachineState.readWord (PaddingTrace.padReturned input).memory
          (Schedule.loadOffsetWord (DriverTrace.messageOffsetWord (start + k)) j).toNat by
    exact statesFrom_wordAbove_pad kernel input start seed inv k _ (hsep j hj)]
  exact hbase j hj

private theorem hashAt32_of_hashWords {input : ByteArray} {n : Nat} {s : State}
    (hw : CSB.HashWordsAt input n s) :
    SRB.hashAt32 s = Compression.embedHash (SRB.hashStateAfter input n) := by
  unfold SRB.hashAt32 StackRunBridge.hashAt32 Compression.embedHash
  rw [show StackRunBridge.wordAt s 352 = OutputTrace.hWord s 0 by rfl,
    show StackRunBridge.wordAt s 384 = OutputTrace.hWord s 1 by rfl,
    show StackRunBridge.wordAt s 416 = OutputTrace.hWord s 2 by rfl,
    show StackRunBridge.wordAt s 448 = OutputTrace.hWord s 3 by rfl,
    show StackRunBridge.wordAt s 480 = OutputTrace.hWord s 4 by rfl,
    hw ⟨0, by omega⟩, hw ⟨1, by omega⟩, hw ⟨2, by omega⟩,
    hw ⟨3, by omega⟩, hw ⟨4, by omega⟩]
  rw [← StackRunBridge.hashArray_hashStateAfter input n]
  rfl

private theorem hashWords_next (kernel : SRB.BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (start : Nat) (seed : State)
    (inv : SeedInvariant input start seed) (k : Nat)
    (hk : start + k < DriverTrace.blockCount input)
    (hw : CSB.HashWordsAt input (start + k)
      (statesFrom kernel input start seed k)) :
    CSB.HashWordsAt input (start + k + 1)
      (statesFrom kernel input start seed (k + 1)) := by
  let h := SRB.hashStateAfter input (start + k)
  let ctx : SRB.BlockContext (statesFrom kernel input start seed k) input
      (start + k) h := {
    calldata := statesFrom_calldata kernel input start seed inv k
    messageBlock := messageBlockAt kernel input hfit start seed inv k hk
    separated := blockSeparated input hfit (start + k) hk
    hash := hashAt32_of_hashWords hw }
  have hout := StackRunBridge.BlockKernel.hashResult kernel
    (statesFrom kernel input start seed k) input (start + k) h hfit hk ctx
    (StackRunBridge.hashArray_hashStateAfter input (start + k))
  have harray := StackRunBridge.hashArray_hashStateAfter input (start + k)
  rw [harray] at hout
  rw [statesFrom]
  intro i
  rw [StackRunBridge.hashAfter_succ]
  fin_cases i
  · exact congrArg Compression.EvmHashState.h0 hout
  · exact congrArg Compression.EvmHashState.h1 hout
  · exact congrArg Compression.EvmHashState.h2 hout
  · exact congrArg Compression.EvmHashState.h3 hout
  · exact congrArg Compression.EvmHashState.h4 hout

theorem statesFrom_hashWords (kernel : SRB.BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (start : Nat) (seed : State)
    (inv : SeedInvariant input start seed) :
    ∀ k, start + k ≤ DriverTrace.blockCount input →
      CSB.HashWordsAt input (start + k) (statesFrom kernel input start seed k) := by
  intro k hk
  induction k with
  | zero => simpa using inv.hashWords
  | succ k ih =>
      have hprev : start + k ≤ DriverTrace.blockCount input := by omega
      have hstrict : start + k < DriverTrace.blockCount input := by omega
      have hs := hashWords_next kernel input hfit start seed inv k hstrict (ih hprev)
      simpa [Nat.add_assoc] using hs

private def rangeAt (kernel : SRB.BlockKernel) (input : ByteArray) (start : Nat)
    (seed : State) (k : Nat) : State :=
  if start + k = DriverTrace.blockCount input then
    DriverTrace.afterExit (statesFrom kernel input start seed k) input
  else
    DriverTrace.loopAt (statesFrom kernel input start seed k) input (start + k)

/-- Run the ordinary driver and packed block kernel over the nonempty global
suffix beginning at `start`.  The strict bound is semantically necessary:
`loopAt ... blockCount` would attempt one block beyond the padded message. -/
def gasSteps_suffix (kernel : SRB.BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (start : Nat) (seed : State)
    (inv : SeedInvariant input start seed)
    (hstart : start < DriverTrace.blockCount input) :
    GasSteps (DriverTrace.loopAt seed input start)
      (DriverTrace.afterExit
        (statesFrom kernel input start seed (DriverTrace.blockCount input - start))
        input) := by
  let count := DriverTrace.blockCount input - start
  have hcount : start + count = DriverTrace.blockCount input := by
    exact Nat.add_sub_of_le (Nat.le_of_lt hstart)
  have hall : GasSteps (rangeAt kernel input start seed 0)
      (rangeAt kernel input start seed count) := by
    apply GasSteps.iterateBounded count
    intro k hk
    have hglobal : start + k < DriverTrace.blockCount input := by omega
    have hnext : start + (k + 1) ≤ DriverTrace.blockCount input := by omega
    let h := SRB.hashStateAfter input (start + k)
    let ctx : SRB.BlockContext (statesFrom kernel input start seed k) input
        (start + k) h := {
      calldata := statesFrom_calldata kernel input start seed inv k
      messageBlock := messageBlockAt kernel input hfit start seed inv k hglobal
      separated := blockSeparated input hfit (start + k) hglobal
      hash := hashAt32_of_hashWords
        (statesFrom_hashWords kernel input hfit start seed inv k (by omega)) }
    have gcompress := StackRunBridge.BlockKernel.gasSteps kernel
      (statesFrom kernel input start seed k) input (start + k) h hfit hglobal ctx
      (statesFrom_code kernel input start seed inv k)
      (statesFrom_fork kernel input start seed inv k)
      (statesFrom_running kernel input start seed inv k)
      (statesFrom_noPrecompile kernel input start seed inv k)
    have gi := DriverTrace.gasSteps_iteration_of_compress
      (statesFrom kernel input start seed k)
      (statesFrom kernel input start seed (k + 1)) input hfit (start + k) hglobal
      (statesFrom_code kernel input start seed inv k)
      (statesFrom_fork kernel input start seed inv k)
      (statesFrom_running kernel input start seed inv k)
      (statesFrom_noPrecompile kernel input start seed inv k)
      (statesFrom_code kernel input start seed inv (k + 1))
      (statesFrom_fork kernel input start seed inv (k + 1))
      (statesFrom_running kernel input start seed inv (k + 1))
      (statesFrom_noPrecompile kernel input start seed inv (k + 1))
      (by simpa [statesFrom] using gcompress)
    exact GasSteps.cast gi
      (by simp [rangeAt, Nat.ne_of_lt hglobal])
      (by simp [rangeAt, DriverTrace.iterationEnd, Nat.add_assoc])
  exact GasSteps.cast hall
    (by simp [rangeAt, Nat.ne_of_lt hstart])
    (by simp only [rangeAt, hcount]; rfl)

/-- Exact final state selected by a suffix run. -/
def finalState (kernel : SRB.BlockKernel) (input : ByteArray) (start : Nat)
    (seed : State) : State :=
  statesFrom kernel input start seed (DriverTrace.blockCount input - start)

theorem finalState_hashWords (kernel : SRB.BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (start : Nat) (seed : State)
    (inv : SeedInvariant input start seed)
    (hstart : start ≤ DriverTrace.blockCount input) :
    CSB.HashWordsAt input (DriverTrace.blockCount input)
      (finalState kernel input start seed) := by
  have hsum : start + (DriverTrace.blockCount input - start) =
      DriverTrace.blockCount input := Nat.add_sub_of_le hstart
  simpa [finalState, hsum] using
    statesFrom_hashWords kernel input hfit start seed inv
      (DriverTrace.blockCount input - start) (by omega)

theorem finalState_executionEnv (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) :
    (finalState kernel input start seed).executionEnv = seed.executionEnv :=
  statesFrom_executionEnv kernel input start seed _

theorem finalState_halt (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) :
    (finalState kernel input start seed).halt = seed.halt :=
  statesFrom_halt kernel input start seed _

theorem finalState_callStack (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) :
    (finalState kernel input start seed).callStack = seed.callStack :=
  statesFrom_callStack kernel input start seed _

theorem finalState_wordAbove_pad (kernel : SRB.BlockKernel) (input : ByteArray)
    (start : Nat) (seed : State) (inv : SeedInvariant input start seed)
    (address : Nat) (haddress : 0x200 ≤ address) :
    SRB.wordAt (finalState kernel input start seed) address =
      SRB.wordAt (PaddingTrace.padReturned input) address :=
  statesFrom_wordAbove_pad kernel input start seed inv _ address haddress

/-- A packaged nonempty suffix certificate for downstream output composition. -/
structure SuffixRun (kernel : SRB.BlockKernel) (input : ByteArray) (start : Nat)
    (seed : State) : Type where
  final : State
  gasSteps : GasSteps (DriverTrace.loopAt seed input start)
    (DriverTrace.afterExit final input)
  executionEnv : final.executionEnv = seed.executionEnv
  halt : final.halt = seed.halt
  callStack : final.callStack = seed.callStack
  wordAbovePad : ∀ address, 0x200 ≤ address →
    SRB.wordAt final address = SRB.wordAt (PaddingTrace.padReturned input) address
  hashWords : CSB.HashWordsAt input (DriverTrace.blockCount input) final

def suffixRun (kernel : SRB.BlockKernel) (input : ByteArray)
    (hfit : CalldataFits input) (start : Nat) (seed : State)
    (inv : SeedInvariant input start seed)
    (hstart : start < DriverTrace.blockCount input) :
    SuffixRun kernel input start seed where
  final := finalState kernel input start seed
  gasSteps := by simpa [finalState] using
    gasSteps_suffix kernel input hfit start seed inv hstart
  executionEnv := finalState_executionEnv kernel input start seed
  halt := finalState_halt kernel input start seed
  callStack := finalState_callStack kernel input start seed
  wordAbovePad := finalState_wordAbove_pad kernel input start seed inv
  hashWords := finalState_hashWords kernel input hfit start seed inv (Nat.le_of_lt hstart)

#print axioms statesFrom_hashWords
#print axioms gasSteps_suffix
#print axioms suffixRun

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSuffixBridge
