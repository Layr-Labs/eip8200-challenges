import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteHigh
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteLow

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

open EvmSemantics
open EvmSemantics.EVM
open WindowNibbleKernel

theorem run_byte (template : State) (pc : UInt256)
    (base modulus word pointer accumulator : UInt256) (rest : List UInt256)
    (index : Nat) (hindex : index < 4) (hrest : rest.length ≤ 1000) :
    runInstructions (byteProgram index)
      (wordKernelState template pc base modulus word pointer accumulator rest) =
    some (wordKernelState template (advancePC (byteAdvance index) pc) base modulus word pointer
      (WindowMath.byteWordStep modulus base accumulator
        (byteValue index word).toNat) rest) := by
  unfold byteProgram
  apply runInstructions_append_some _ _ _ _ _
    (run_high template pc base modulus word pointer accumulator rest index hindex
      hrest)
  simpa only [← advancePC_add,
      show highPrepAdvance index + 35 + 42 = byteAdvance index by
        unfold byteAdvance
        omega,
      WindowMath.byteWordStep, highNibble, lowNibble] using
    run_low template (advancePC (highPrepAdvance index + 35) pc) base modulus
      (highNibble index word) index word pointer
      (WindowMath.nibbleWordStep modulus base accumulator
        (highNibble index word)) rest hrest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel
