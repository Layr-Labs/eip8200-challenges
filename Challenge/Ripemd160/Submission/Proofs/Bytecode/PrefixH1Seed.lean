import Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixBranchSite
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedSuffixBridge

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000

/-!
# H1 prefix branch as a seeded suffix run

The appended prefix branch does not finish RIPEMD-160.  On recognition it
installs the chaining state after padded block zero and jumps to the existing
driver post-check at PC `466`.  That post-check advances the block offset to
one; the ordinary packed block kernel must then process every remaining global
block.

This file packages precisely that seam.  Branch execution itself remains in
`PrefixBranchSite`, and suffix execution remains in `PackedSuffixBridge`.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixH1Seed

open Challenge.Ripemd160
open Challenge.EvmProof
open EvmSemantics
open EvmSemantics.EVM

/-- State at the first H1 store.  The prefix comparisons have already consumed
all temporary stack values, so the padding driver's two-word stack remains. -/
def storeEntry (input : ByteArray) : State :=
  { PaddingTrace.padBranchReturned input with pc := UInt256.ofNat 5450 }

/-- The state returned by the five H1 stores and their jump to PC `466`. -/
def seed (input : ByteArray) : State :=
  PrefixBranchSite.afterStores (storeEntry input)

@[simp] theorem seed_pc (input : ByteArray) :
    (seed input).pc = UInt256.ofNat 466 := by
  rfl

@[simp] theorem seed_stack (input : ByteArray) :
    (seed input).stack = [UInt256.ofNat 0, Padding.paddedWord input] := by
  rfl

@[simp] theorem seed_memory (input : ByteArray) :
    (seed input).memory =
      PrefixBranch.branchMemory (PaddingTrace.padReturned input).memory := by
  rfl

@[simp] theorem seed_executionEnv (input : ByteArray) :
    (seed input).executionEnv = (PaddingTrace.padReturned input).executionEnv := by
  rfl

@[simp] theorem seed_calldata (input : ByteArray) :
    (seed input).executionEnv.calldata = input := by
  rfl

@[simp] theorem seed_code (input : ByteArray) :
    (seed input).executionEnv.code = submissionBytecode := by
  simpa only [seed_executionEnv] using PaddingTrace.padReturned_code input

@[simp] theorem seed_fork (input : ByteArray) :
    (seed input).fork = .Osaka := by
  simpa only [seed_executionEnv] using PaddingTrace.padReturned_fork input

@[simp] theorem seed_running (input : ByteArray) :
    (seed input).halt = .Running := by
  rfl

@[simp] theorem seed_noPrecompile (input : ByteArray) :
    Precompile.isPrecompileWithConfig (seed input).executionEnv.precompileConfig
      (seed input).executionEnv.fork (seed input).executionEnv.codeAddr = false := by
  simpa only [seed_executionEnv] using PaddingTrace.padReturned_noPrecompile input

@[simp] theorem seed_callStack (input : ByteArray) :
    (seed input).callStack = [] := by
  rfl

/-- The five stores do not alter any padded-message word. -/
theorem seed_wordAbovePad (input : ByteArray) (address : Nat)
    (haddress : 0x200 ≤ address) :
    StackRunBridge.wordAt (seed input) address =
      StackRunBridge.wordAt (PaddingTrace.padReturned input) address := by
  simpa only [StackRunBridge.wordAt, seed_memory] using
    PrefixBranch.branchMemory_read_above
      (PaddingTrace.padReturned input).memory address haddress

/-- Recognition guarantees that the padded image contains at least two
blocks.  Thus the hit path always has a genuine suffix beginning at block one. -/
theorem start_lt (input : ByteArray) (hrec : PrefixBranch.Recognised input) :
    1 < DriverTrace.blockCount input := by
  have hsize : 64 ≤ input.size := PrefixBranch.recognised_size input hrec
  simp only [DriverTrace.blockCount, Padding.paddedLength, Nat.mul_div_right]
  omega

/-- The five stored words are exactly the mathematical chaining state after
global block zero. -/
theorem seed_hashWords (input : ByteArray) (hrec : PrefixBranch.Recognised input) :
    CompressionSeamBridge.HashWordsAt input 1 (seed input) := by
  have hstored := PrefixBranch.branchMemory_hashAt
    (PaddingTrace.padReturned input).memory
  have hmath : CompressionSeamBridge.hashAfter input 1 = PatternedDigest.H1 := by
    rw [StackRunBridge.hashAfter_succ]
    simpa [CompressionSeamBridge.hashAfter, SpecBridge.absorbBlocks,
      PatternedDigest.H0] using PrefixBranch.branch_stores_first_block input hrec
  rw [hmath]
  intro i
  fin_cases i
  · change (StackMemory.hashAt (seed input).memory).h0 = _
    rw [seed_memory, hstored]
  · change (StackMemory.hashAt (seed input).memory).h1 = _
    rw [seed_memory, hstored]
  · change (StackMemory.hashAt (seed input).memory).h2 = _
    rw [seed_memory, hstored]
  · change (StackMemory.hashAt (seed input).memory).h3 = _
    rw [seed_memory, hstored]
  · change (StackMemory.hashAt (seed input).memory).h4 = _
    rw [seed_memory, hstored]

/-- The exact invariant consumed by `PackedSuffixBridge.suffixRun` at global
block index one. -/
def seedInvariant (input : ByteArray) (hrec : PrefixBranch.Recognised input) :
    PackedSuffixBridge.SeedInvariant input 1 (seed input) where
  calldata := seed_calldata input
  code := seed_code input
  fork := seed_fork input
  running := seed_running input
  noPrecompile := seed_noPrecompile input
  callStack := seed_callStack input
  wordAbovePad := seed_wordAbovePad input
  hashWords := seed_hashWords input hrec

theorem seed_eq_compressReturned (input : ByteArray) :
    seed input = DriverTrace.compressReturned (seed input) input 0 := by
  unfold seed PrefixBranchSite.afterStores storeEntry DriverTrace.compressReturned
  simp only [PrefixBranch.loopHeadPC, DriverTrace.blockOffsetWord,
    DriverTrace.blockOffset, PaddingTrace.padBranchReturned_stack]

/-- Full hit path through padding, recognition, H1 stores and the existing
post-check.  The result is the ordinary driver loop at global block one. -/
noncomputable def gasSteps_hit_to_loop (input : ByteArray)
    (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0)
      (Execution.atPC input 0x16c))
    (hrec : PrefixBranch.Recognised input) :
    GasSteps (initialState submissionBytecode input 0)
      (DriverTrace.loopAt (seed input) input 1) := by
  have gpad := PaddingTrace.gasSteps_padToBranch input hfit entryPrefix
  have ghit := PrefixBranchSite.gasSteps_hit
    (hfit := hfit)
    (PaddingTrace.padBranchReturned input) input
    [UInt256.ofNat 0, Padding.paddedWord input]
    (by simpa using PaddingTrace.padReturned_code input)
    (by simpa using PaddingTrace.padReturned_fork input)
    (by simpa using PaddingTrace.padReturned_noPrecompile input)
    (by rfl) (PaddingTrace.padBranchReturned_pc input)
    (PaddingTrace.padBranchReturned_stack input) (by rfl) (by decide)
    (not_lt_of_ge (PrefixBranch.recognised_size input hrec)) hrec
  have ghit' : GasSteps (PaddingTrace.padBranchReturned input)
      (DriverTrace.compressReturned (seed input) input 0) :=
    GasSteps.cast ghit rfl (by
      rw [← seed_eq_compressReturned input]
      rfl)
  have gcontinue := DriverTrace.gasSteps_postCheck_continue (seed input) input
    hfit 0 (start_lt input hrec) (seed_code input) (seed_fork input)
    (seed_running input) (seed_noPrecompile input)
  exact gpad.trans (ghit'.trans gcontinue)

#print axioms seed_hashWords
#print axioms seedInvariant
#print axioms gasSteps_hit_to_loop

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PrefixH1Seed
