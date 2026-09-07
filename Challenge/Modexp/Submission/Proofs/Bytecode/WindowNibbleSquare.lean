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

private def squareTopState (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256) : State :=
  { nibbleState template pc base modulus nibble byte word pointer original rest with
    stack := [accumulator, UInt256.ofNat nibble, byte, word, pointer, original, modulus] ++ rest }

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
private theorem run_finishSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions finishSquareProgram
      (squareTopState template pc base modulus nibble byte word pointer original accumulator rest) =
    some (nibbleState template (advancePC 8 pc) base modulus nibble byte word pointer
      accumulator rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, finishSquareProgram, squareTopState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

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
    runInstructions_append, runInstructions_append,
    run_beginSquare template pc base modulus nibble byte word pointer accumulator rest hrest]
  simp only [Option.bind_some]
  rw [run_topSquare (hrest := hrest)]
  simp only [Option.bind_some]
  rw [run_topSquare (hrest := hrest)]
  simp only [Option.bind_some]
  rw [run_topSquare (hrest := hrest)]
  simp only [Option.bind_some]
  rw [run_finishSquare (hrest := hrest)]
  rw [show advancePC 8 (advancePC 4 (advancePC 4 (advancePC 4 (advancePC 4 pc)))) =
      advancePC 24 pc by
    rw [← advancePC_add, ← advancePC_add, ← advancePC_add, ← advancePC_add]]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
