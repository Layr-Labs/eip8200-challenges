import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerPersistentStart
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

noncomputable def gasSteps_start (input : ByteArray) (hfit : CalldataFits input)
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 272)) :
    GasSteps (initialState submissionBytecode input 0)
      (loopState (PaddingTrace.padReturned input) StackRunBridge.initialHashState 0
        (DriverTrace.blockCount input) []) := by
  let s := PaddingTrace.padReturned input
  have gp := PaddingTrace.gasSteps_pad input hfit entryPrefix
  have gi := StaggerPersistentStart.gasSteps s (UInt256.ofNat 0) (Padding.paddedWord input) []
    (by decide) (PaddingTrace.padReturned_halt input) (PaddingTrace.padReturned_code input)
    (PaddingTrace.padReturned_fork input) (PaddingTrace.padReturned_noPrecompile input)
  have gj := StaggerPersistentLoopSites.gasSteps_join s
    (StaggerPersistentFrame.frame StackRunBridge.initialHashState (UInt256.ofNat 0) (Padding.paddedWord input) [])
    (by simp [StaggerPersistentFrame.frame]) (PaddingTrace.padReturned_halt input) (PaddingTrace.padReturned_code input)
    (PaddingTrace.padReturned_fork input) (PaddingTrace.padReturned_noPrecompile input)
  have gs : s = {s with pc := UInt256.ofNat 331, stack := [UInt256.ofNat 0, Padding.paddedWord input]} := rfl
  rw [← gs] at gi
  have g := gp.trans (gi.trans gj)
  simpa only [loopState, offsetWord, Nat.zero_mul, limit_eq input hfit] using g

def result (input : ByteArray) (states : Nat → State) (hashes : Nat → Compression.HashState) : State :=
  StaggerPersistentSerialize.result (states (DriverTrace.blockCount input))
    (hashes (DriverTrace.blockCount input))
    (limitWord (DriverTrace.blockCount input)) (limitWord (DriverTrace.blockCount input)) []

noncomputable def fullTrace (input : ByteArray) (hfit : CalldataFits input)
    (states : Nat → State) (hashes : Nat → Compression.HashState)
    (hszero : states 0 = PaddingTrace.padReturned input)
    (hhzero : hashes 0 = StackRunBridge.initialHashState)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient (states i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState (states i) (hashes i) i (DriverTrace.blockCount input) [])
        (postState (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) []))
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 272)) :
    GasSteps (initialState submissionBytecode input 0) (result input states hashes) := by
  have gs := gasSteps_start input hfit entryPrefix
  have gb := run_blocks states hashes (DriverTrace.blockCount input) []
    (DriverTrace.blockCount_pos input) (padded_bound input hfit) (by decide) hambient hblock
  have a := hambient (DriverTrace.blockCount input) (Nat.le_refl _)
  have go := StaggerPersistentSerialize.gasSteps (states (DriverTrace.blockCount input))
    (limitWord (DriverTrace.blockCount input)) (limitWord (DriverTrace.blockCount input))
    (hashes (DriverTrace.blockCount input)) [] (by decide) a.running a.code a.fork a.notPrecompile
  rw [← hszero, ← hhzero] at gs
  exact gs.trans (gb.trans go)

theorem correct_of_blocks (input : ByteArray) (hfit : CalldataFits input)
    (states : Nat → State) (hashes : Nat → Compression.HashState)
    (hszero : states 0 = PaddingTrace.padReturned input)
    (hhzero : hashes 0 = StackRunBridge.initialHashState)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient (states i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState (states i) (hashes i) i (DriverTrace.blockCount input) [])
        (postState (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) []))
    (hfinal : CompressionCorrect.hashArray (hashes (DriverTrace.blockCount input)) =
      CompressionSeamBridge.hashAfter input (DriverTrace.blockCount input))
    (hcalls : (states (DriverTrace.blockCount input)).callStack = [])
    (entryPrefix : GasSteps (initialState submissionBytecode input 0) (Execution.atPC input 272)) :
    ∃ g₀ : Nat, ∀ gas : Nat, g₀ ≤ gas →
      Eval (initialState submissionBytecode input gas) (.returned (spec input)) := by
  let trace := fullTrace input hfit states hashes hszero hhzero hambient hblock entryPrefix
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
