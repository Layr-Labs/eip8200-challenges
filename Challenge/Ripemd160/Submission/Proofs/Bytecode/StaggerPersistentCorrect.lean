import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadSkipEntry
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentLoopInduction
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentSerializeMath
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.GasCost
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCorrect
open Challenge.Ripemd160 EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open StaggerPersistentLoopInduction

theorem padded_bound (input : ByteArray) (hfit : CalldataFits input) :
    DriverTrace.blockCount input * 64 < 2^256 := by
  rw [← DriverTrace.paddedLength_eq_blockCount]
  have h := Padding.paddedLength_lt input.size
  have hf : input.size < 2^64 := hfit
  have hb : 2^64 + 73 < (2:Nat)^256 := by decide
  omega

theorem limit_eq (input : ByteArray) (hfit : CalldataFits input) :
    limitWord (DriverTrace.blockCount input) = Padding.paddedWord input := by
  rw [Padding.paddedWord_eq input hfit]
  unfold limitWord
  rw [DriverTrace.paddedLength_eq_blockCount]

noncomputable def gasSteps_start (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 497)) :
    GasSteps (initialState submissionBytecode input 0)
      (loopState input (PaddingTrace.entryState input) StackRunBridge.initialHashState 0
        (DriverTrace.blockCount input) []) := by
  let s := PaddingTrace.entryState input
  let h := StackRunBridge.initialHashState
  have hr : s.halt = .Running := PadSkipEntry.entryState_halt input
  have hc : s.executionEnv.code = Artifact.submissionArtifact.code := PadSkipEntry.entryState_code input
  have hf : s.fork = .Osaka := PadSkipEntry.entryState_fork input
  have hn : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := PadSkipEntry.entryState_noPrecompile input
  have hi : s.executionEnv.calldata = input := PadSkipEntry.entryState_calldata input
  have heta := PaddingTrace.entryState_eta input
  have gx : GasSteps s {s with pc := UInt256.ofNat 629, stack := StaggerPersistentFrame.frame h (UInt256.ofNat 0) (LoopCompletionControl.limit input) []} := by
    by_cases hz : input.size % 64 = 0
    · have hs : s = {s with pc := UInt256.ofNat 520, stack := [Padding.paddedWord input]} := by
        simpa only [if_pos hz, PaddingTrace.padFrame] using heta
      have gf := StaggerPersistentStart.gasSteps_full s (Padding.paddedWord input) []
        (by decide) hr hc hf hn
      rw [hi] at gf
      have gi := StaggerPersistentStart.gasSteps_push s (UInt256.ofNat input.size) []
        (by decide) hr hc hf hn
      have g := gf.trans gi
      rw [← hs] at g
      simpa only [LoopCompletionControl.limit, LoopCompletionControl.limitNat, if_pos hz] using g
    · have hs : s = {s with pc := UInt256.ofNat 522, stack := [Padding.paddedWord input]} := by
        simpa only [if_neg hz, PaddingTrace.padFrame] using heta
      have gi := StaggerPersistentStart.gasSteps_push s (Padding.paddedWord input) []
        (by decide) hr hc hf hn
      rw [← hs] at gi
      simpa only [LoopCompletionControl.limit, LoopCompletionControl.limitNat, if_neg hz,
        Padding.paddedWord_eq input hfit] using gi
  have gj := StaggerPersistentLoopSites.gasSteps_join s
    (StaggerPersistentFrame.frame h (UInt256.ofNat 0) (LoopCompletionControl.limit input) [])
    (by simp [StaggerPersistentFrame.frame]) hr hc hf hn
  have gp := PaddingTrace.gasSteps_pad input hfit entryPrefix
  have g := gp.trans (gx.trans gj)
  simpa only [loopState, LoopCompletionControl.blockPC, Nat.zero_mul,
    if_neg (show input.size ≠ 0 by omega), offsetWord] using g

def result (input : ByteArray) (states : Nat → State) (hashes : Nat → Compression.HashState) : State :=
  StaggerPersistentSerialize.result (states (DriverTrace.blockCount input))
    (hashes (DriverTrace.blockCount input))
    (limitWord (DriverTrace.blockCount input)) (LoopCompletionControl.limit input) []

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (states : Nat → State) (hashes : Nat → Compression.HashState)
    (hszero : states 0 = PaddingTrace.entryState input)
    (hhzero : hashes 0 = StackRunBridge.initialHashState)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient input (states i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states i) (hashes i) i (DriverTrace.blockCount input) [])
        (postState input (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) []))
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 497)) :
    GasSteps (initialState submissionBytecode input 0) (result input states hashes) := by
  have gs := gasSteps_start input hfit hpositive entryPrefix
  have gb := run_blocks input states hashes [] hfit (by decide) hambient hblock
  have a := hambient (DriverTrace.blockCount input) (Nat.le_refl _)
  have go := StaggerPersistentSerialize.gasSteps (states (DriverTrace.blockCount input))
    (limitWord (DriverTrace.blockCount input)) (LoopCompletionControl.limit input)
    (hashes (DriverTrace.blockCount input)) [] (by decide) a.running a.code a.fork a.notPrecompile
  rw [← hszero, ← hhzero] at gs
  exact gs.trans (gb.trans go)

theorem correct_of_blocks (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (states : Nat → State) (hashes : Nat → Compression.HashState)
    (hszero : states 0 = PaddingTrace.entryState input)
    (hhzero : hashes 0 = StackRunBridge.initialHashState)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient input (states i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState input (states i) (hashes i) i (DriverTrace.blockCount input) [])
        (postState input (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) []))
    (hfinal : CompressionCorrect.hashArray (hashes (DriverTrace.blockCount input)) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input))
    (hcalls : (states (DriverTrace.blockCount input)).callStack = [])
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 497)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := fullTrace input hfit hpositive states hashes hszero hhzero hambient hblock entryPrefix
  have hr : (result input states hashes).halt = .Returned := rfl
  have hc : (result input states hashes).callStack = [] := hcalls
  have hb : (result input states hashes).hReturn = spec input :=
    StaggerPersistentSerialize.returned_spec_of_hashArray _ input _ _ [] _ hfinal
  refine ⟨trace.cost, fun gas hgas => ?_⟩
  have heval := eval_of_steps (trace.trace gas hgas) (by
    simp [withGas, State.isDone, State.isHalted, State.isRunning, hc, hr])
  rw [State.toResult_returned _ (by exact hr)] at heval
  change Eval (withGas (initialState submissionBytecode input 0) gas)
    (.returned (result input states hashes).hReturn) at heval
  rw [hb] at heval
  simpa only [GasCost.withGas_initialState_zero] using heval
#print axioms correct_of_blocks
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentCorrect
