import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopControl
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitWordStep

set_option warningAsError true

/-!
# Eight-word fixed-width loop

The loop is composed at opaque guard, word, and advance contracts.  No
concrete artifact segment is unfolded here.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopBody

open EvmSemantics
open EvmSemantics.EVM
open WindowHitStates

def loopAccumulator (input : ByteArray) (count : Nat) : UInt256 :=
  WindowMath.afterChunksWord input 128 (modulusWord input) (baseWord input)
    count (UInt256.ofNat 1)

def gasSteps_iteration (input : ByteArray) (count : Nat) (hcount : count < 8) :
    Challenge.EvmProof.GasSteps
      (loopState input (128 + 4 * count) (loopAccumulator input count))
      (loopState input (128 + 4 * (count + 1))
        (loopAccumulator input (count + 1))) := by
  have hpointer : 128 + 4 * count < 160 := by omega
  have hguard := WindowHitLoopControl.gasSteps_loopContinue input
    (128 + 4 * count) (loopAccumulator input count) hpointer
  have hword := WindowHitWordStep.gasSteps_word input (128 + 4 * count)
    (loopAccumulator input count) hpointer
  have hnext : 128 + 4 * count + 4 = 128 + 4 * (count + 1) := by omega
  simpa only [loopAccumulator, WindowMath.afterChunksWord, hnext] using
    hguard.trans hword

def gasSteps_loop (input : ByteArray) :
    Challenge.EvmProof.GasSteps
      (loopState input 128 (UInt256.ofNat 1))
      (finishState input (loopAccumulator input 8)) := by
  have h0 := gasSteps_iteration input 0 (by decide)
  have h1 := gasSteps_iteration input 1 (by decide)
  have h2 := gasSteps_iteration input 2 (by decide)
  have h3 := gasSteps_iteration input 3 (by decide)
  have h4 := gasSteps_iteration input 4 (by decide)
  have h5 := gasSteps_iteration input 5 (by decide)
  have h6 := gasSteps_iteration input 6 (by decide)
  have h7 := gasSteps_iteration input 7 (by decide)
  have hbody := (((((((h0.trans h1).trans h2).trans h3).trans h4).trans h5).trans
    h6).trans h7)
  have hexit := WindowHitLoopControl.gasSteps_loopExit input
    (loopAccumulator input 8)
  simpa only [loopAccumulator, WindowMath.afterChunksWord] using hbody.trans hexit

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopBody
