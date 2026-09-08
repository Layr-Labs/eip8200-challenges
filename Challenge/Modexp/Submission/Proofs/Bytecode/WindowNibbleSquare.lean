import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleFused

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM

private theorem run_stagedPair (template : State) (pc a m : UInt256)
    (tail : List UInt256) (h : tail.length ≤ 1010) :
    runInstructions [.op (.Dup ⟨0, by decide⟩), .op .MULMOD]
      { template with pc := pc, stack := a :: m :: tail } =
    some { template with
      pc := advancePC 2 pc
      stack := UInt256.mulMod a a m :: tail } := by
  have h2 : tail.length + 1 + 1 < 1024 := by omega
  have h3 : tail.length + 1 + 1 + 1 < 1024 := by omega
  simp (disch := omega) [runInstructions, Challenge.EvmProof.Stepper.runInstr,
    advancePC, h2, h3, List.getElem?_cons_zero]

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
/-- The four pure squarings reduce in one pass to the seven-slot square state
holding `squareWordAfter modulus 4 accumulator`: thirteen instructions, thirteen
bytes, peak depth twelve plus `rest`. -/
theorem run_fourSquares_frame (template : State) (pc modulus nibble : UInt256)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions fourSquareProgram
      { template with
        pc := pc
        stack := [nibble, byte, word, pointer, accumulator, modulus] ++ rest } =
      some { template with
        pc := advancePC 13 pc
        stack := [WindowMath.squareWordAfter modulus 4 accumulator,
          nibble, byte, word, pointer, accumulator, modulus] ++ rest } := by
  let start : State := { template with
    pc := pc
    stack := [nibble, byte, word, pointer, accumulator, modulus] ++ rest }
  have stage : runInstructions (fourSquareProgram.take 5) start =
      some { start with
        pc := advancePC 5 pc
        stack := accumulator :: modulus :: modulus :: modulus :: modulus :: start.stack } := by
    have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    simp (config := { maxSteps := 100000 }) (disch := omega)
      [fourSquareProgram, runInstructions, start,
        Challenge.EvmProof.Stepper.runInstr, advancePC,
        h6, h7, h8, h9, h10, List.getElem?_cons_zero, List.getElem?_cons_succ]
  change runInstructions
    ((fourSquareProgram.take 5) ++
      [.op (.Dup ⟨0, by decide⟩), .op .MULMOD] ++
      [.op (.Dup ⟨0, by decide⟩), .op .MULMOD] ++
      [.op (.Dup ⟨0, by decide⟩), .op .MULMOD] ++
      [.op (.Dup ⟨0, by decide⟩), .op .MULMOD]) start = _
  rw [runInstructions_append, runInstructions_append, runInstructions_append,
    runInstructions_append, stage]
  simp only [Option.bind_some]
  rw [run_stagedPair start (advancePC 5 pc) accumulator modulus
    (modulus :: modulus :: modulus :: start.stack) (by simp [start]; omega)]
  simp only [Option.bind_some]
  rw [run_stagedPair start (advancePC 2 (advancePC 5 pc))
    (UInt256.mulMod accumulator accumulator modulus) modulus
    (modulus :: modulus :: start.stack) (by simp [start]; omega)]
  simp only [Option.bind_some]
  rw [run_stagedPair start (advancePC 2 (advancePC 2 (advancePC 5 pc)))
    (UInt256.mulMod (UInt256.mulMod accumulator accumulator modulus)
      (UInt256.mulMod accumulator accumulator modulus) modulus) modulus
    (modulus :: start.stack) (by simp [start]; omega)]
  simp only [Option.bind_some]
  rw [run_stagedPair start (advancePC 2 (advancePC 2 (advancePC 2 (advancePC 5 pc))))
    (UInt256.mulMod
      (UInt256.mulMod (UInt256.mulMod accumulator accumulator modulus)
        (UInt256.mulMod accumulator accumulator modulus) modulus)
      (UInt256.mulMod (UInt256.mulMod accumulator accumulator modulus)
        (UInt256.mulMod accumulator accumulator modulus) modulus) modulus) modulus
    start.stack (by simp [start]; omega)]
  rfl

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
  exact run_fourSquares_frame
    { template with
      memory := WindowTableMemory.tableMemory base modulus
      activeWords := UInt256.ofNat 16 }
    pc modulus (UInt256.ofNat nibble) byte word pointer accumulator rest hrest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
