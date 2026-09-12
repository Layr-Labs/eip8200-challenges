import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBytePrep

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

open EvmSemantics
open EvmSemantics.EVM
open WindowNibbleKernel

theorem run_low (template : State) (pc : UInt256)
    (base modulus : UInt256) (high index : Nat)
    (word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions lowProgram
      (droppedNibbleState template pc base modulus high (byteValue index word) word
        pointer accumulator rest) =
    some (wordKernelState template (advancePC 25 pc) base modulus word pointer
      (WindowMath.nibbleWordStep modulus base accumulator
        (lowNibble index word)) rest) := by
  unfold lowProgram
  apply runInstructions_append_some _ _ _ _ _
    (runInstructions_append_some _ _ _ _ _
      (run_lowPrep template pc base modulus high index word pointer accumulator
        rest hrest)
      (run_lowSquareLookup template (advancePC 3 pc) base modulus
        (lowNibble index word) (byteValue index word) word pointer accumulator
        rest (lowNibble_lt index word) hrest))
  simpa only [← advancePC_add, show 3 + 22 + 0 = 25 by decide] using
    run_finish template
      (advancePC 22 (advancePC 3 pc)) base modulus (lowNibble index word)
      (byteValue index word) word pointer
      (WindowMath.nibbleWordStep modulus base accumulator
        (lowNibble index word)) rest hrest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel
