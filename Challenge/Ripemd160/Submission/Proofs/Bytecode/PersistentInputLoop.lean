import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentLoopInduction
set_option warningAsError true
set_option maxHeartbeats 4000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentInputLoop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open PersistentLoopInduction

def postState (s : State) (input : ByteArray) (i : Nat)
    (h : Compression.HashState) (rho : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 490
    stack := PersistentFrame.frame h (DriverTrace.blockOffsetWord i) (Padding.paddedWord input) rho}

def exitState (s : State) (input : ByteArray) (h : Compression.HashState)
    (rho : List UInt256) : State :=
  {s with
    pc := UInt256.ofNat 4704
    stack := PersistentFrame.frame h (Padding.paddedWord input) (Padding.paddedWord input) rho}

def run_input_blocks (states : Nat → State) (hashes : Nat → Compression.HashState)
    (input : ByteArray) (rho : List UInt256) (hfit : input.size < 2^64)
    (hstack : rho.length ≤ 980)
    (hambient : ∀ i, i ≤ DriverTrace.blockCount input → Ambient (states i))
    (hblock : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (Table144CallPrepare.callState (states i) input i (hashes i) rho)
        (postState (states (i + 1)) input i (hashes (i + 1)) rho)) :
    GasSteps (Table144CallPrepare.callState (states 0) input 0 (hashes 0) rho)
      (exitState (states (DriverTrace.blockCount input)) input (hashes (DriverTrace.blockCount input)) rho) := by
  have hp : Padding.paddedWord input = limitWord (DriverTrace.blockCount input) := by
    rw [Padding.paddedWord_eq input hfit, DriverTrace.paddedLength_eq_blockCount]
    rfl
  have hb : DriverTrace.blockCount input * 64 < 2^256 := by
    have hl := Padding.paddedLength_lt input.size
    rw [DriverTrace.paddedLength_eq_blockCount] at hl
    omega
  have hbody : ∀ i, i < DriverTrace.blockCount input →
      GasSteps (loopState (states i) (hashes i) i (DriverTrace.blockCount input) rho)
        (PersistentLoopInduction.postState (states (i + 1)) (hashes (i + 1)) i (DriverTrace.blockCount input) rho) := by
    intro i hi
    simpa only [Table144CallPrepare.callState, loopState, PersistentLoopInduction.postState,
      postState, hp, DriverTrace.blockOffsetWord, DriverTrace.blockOffset, offsetWord] using hblock i hi
  have g := run_blocks states hashes (DriverTrace.blockCount input) rho
    (DriverTrace.blockCount_pos input) hb hstack hambient hbody
  simpa only [Table144CallPrepare.callState, loopState, PersistentLoopInduction.exitState,
    exitState, hp, DriverTrace.blockOffsetWord, DriverTrace.blockOffset, offsetWord] using g

#print axioms run_input_blocks
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentInputLoop
