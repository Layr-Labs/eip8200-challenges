import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleSquare
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleLookup

set_option warningAsError true

/-!
# Artifact-independent four-bit execution kernel

The concrete bytecode repeats this instruction sequence for each high and low
nibble.  The square and lookup reductions live in separate modules so each
elaboration remains bounded.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_squareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions squareLookupProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (nibbleState template (advancePC 35 pc) base modulus nibble
        byte word pointer
        (WindowMath.nibbleWordStep modulus base accumulator nibble) rest) := by
  rw [squareLookupProgram, runInstructions_append,
    run_fourSquares template pc base modulus nibble byte word pointer
      accumulator rest hrest]
  simp only [Option.bind_some]
  rw [run_lookup template (advancePC 24 pc) base modulus nibble byte word
    pointer (WindowMath.squareWordAfter modulus 4 accumulator) rest hnibble
    hrest]
  rw [← advancePC_add]
  norm_num
  unfold WindowMath.nibbleWordStep
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
