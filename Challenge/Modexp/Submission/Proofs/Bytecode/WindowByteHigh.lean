import Challenge.Modexp.Submission.Proofs.Bytecode.WindowBytePrep

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

open EvmSemantics
open EvmSemantics.EVM
open WindowNibbleKernel

theorem run_high (template : State) (pc : UInt256)
    (base modulus word pointer accumulator : UInt256) (rest : List UInt256)
    (index : Nat) (hindex : index < 4) (hrest : rest.length ≤ 1000) :
    runInstructions (highProgram index)
      (wordKernelState template pc base modulus word pointer accumulator rest) =
    some (nibbleState template
      (advancePC (highPrepAdvance index + 35) pc) base modulus
      (highNibble index word) (byteValue index word) word pointer
      (WindowMath.nibbleWordStep modulus base accumulator
        (highNibble index word)) rest) := by
  unfold highProgram
  apply runInstructions_append_some _ _ _ _ _
    (run_highPrep template pc base modulus word pointer accumulator rest index
      hindex hrest)
  simpa only [← advancePC_add] using
    run_squareLookup template (advancePC (highPrepAdvance index) pc)
      base modulus (highNibble index word) (byteValue index word) word pointer
      accumulator rest (highNibble_lt index word hindex) hrest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel
