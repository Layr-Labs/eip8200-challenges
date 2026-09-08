import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleFused
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSquareBatch

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

set_option linter.unusedSimpArgs false in
private theorem run_beginSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions beginSquareProgram
      (nibbleState template pc base modulus nibble byte word pointer accumulator rest) =
    some (squareTopState template (advancePC 4 pc) base modulus nibble byte word pointer
      accumulator (UInt256.mulMod accumulator accumulator modulus) rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, beginSquareProgram, squareTopState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

set_option linter.unusedSimpArgs false in
private theorem run_topSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions topSquareProgram
      (squareTopState template pc base modulus nibble byte word pointer original accumulator rest) =
    some (squareTopState template (advancePC 4 pc) base modulus nibble byte word pointer
      original (UInt256.mulMod accumulator accumulator modulus) rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, topSquareProgram, squareTopState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

set_option linter.unusedSimpArgs false in
/-- The four pure squarings reduce in one pass to the seven-slot square state
holding `squareWordAfter modulus 4 accumulator`: thirteen instructions, thirteen
bytes, peak depth twelve plus `rest`. -/
theorem run_fourSquares (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions fourSquareProgram
      (nibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (squareTopState template (advancePC 13 pc) base modulus nibble
        byte word pointer accumulator
        (WindowMath.squareWordAfter modulus 4 accumulator) rest) := by
  simpa only [fourSquareProgram, WindowSquareBatch.program6, WindowSquareBatch.stage6,
    WindowSquareBatch.pair, WindowSquareBatch.framed, nibbleState, squareTopState,
    List.cons_append, List.nil_append] using
    WindowSquareBatch.run_batch6
      (nibbleState template pc base modulus nibble byte word pointer accumulator rest)
      pc (UInt256.ofNat nibble) byte word pointer accumulator modulus rest hrest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
