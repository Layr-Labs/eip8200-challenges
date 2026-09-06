import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleDefs

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_square (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions squareProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (nibbleState template (advancePC 6 pc) base modulus nibble
        byte word pointer (UInt256.mulMod accumulator accumulator modulus)
        rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, squareProgram, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      advancePC]

theorem run_fourSquares (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions fourSquareProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (nibbleState template (advancePC 24 pc) base modulus nibble
        byte word pointer (WindowMath.squareWordAfter modulus 4 accumulator)
        rest) := by
  rw [fourSquareProgram, runInstructions_append, runInstructions_append,
    runInstructions_append,
    run_square template pc base modulus nibble byte word pointer accumulator
      rest hrest]
  simp only [Option.bind_some]
  rw [run_square (hrest := hrest)]
  simp only [Option.bind_some]
  rw [run_square (hrest := hrest)]
  simp only [Option.bind_some]
  rw [run_square (hrest := hrest)]
  rw [show advancePC 6 (advancePC 6 (advancePC 6 (advancePC 6 pc))) =
      advancePC 24 pc by
    rw [← advancePC_add, ← advancePC_add, ← advancePC_add]]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
