import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleFused

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

/-- State between the prepare step and the last cached square: the working
accumulator sits on `cache` spare modulus copies above the untouched input
frame. -/
private def cacheSquareState (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256)
    (cache : List UInt256) (rest : List UInt256) : State :=
  { nibbleState template pc base modulus nibble byte word pointer original rest with
    stack := accumulator :: (cache ++
      [UInt256.ofNat nibble, byte, word, pointer, original, modulus] ++ rest) }

set_option linter.unusedSimpArgs false in
private theorem run_prepareSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions prepareSquaresProgram
      (nibbleState template pc base modulus nibble byte word pointer accumulator rest) =
    some (cacheSquareState template (advancePC 6 pc) base modulus nibble byte word
      pointer accumulator accumulator [modulus, modulus, modulus, modulus, modulus] rest) := by
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  have h11 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, prepareSquaresProgram, cacheSquareState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h6, h7, h8, h9, h10, h11,
      List.getElem?_cons_zero, List.getElem?_cons_succ, advancePC]

set_option linter.unusedSimpArgs false in
private theorem run_cachedSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256)
    (cache : List UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hcache : cache.length ≤ 4) :
    runInstructions cachedSquareProgram
      (cacheSquareState template pc base modulus nibble byte word pointer original
        accumulator (modulus :: cache) rest) =
    some (cacheSquareState template (advancePC 2 pc) base modulus nibble byte word
      pointer original (UInt256.mulMod accumulator accumulator modulus) cache rest) := by
  have h2 : cache.length + (rest.length + 1 + 1 + 1 + 1 + 1 + 1) + 1 + 1 < 1024 := by omega
  have h3 : cache.length + (rest.length + 1 + 1 + 1 + 1 + 1 + 1) + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, cachedSquareProgram, cacheSquareState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, hcache, h2, h3,
      List.length_append, List.getElem?_cons_zero, List.getElem?_cons_succ, advancePC]

theorem run_fourSquares (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions fourSquareProgram
      (nibbleState template pc base modulus nibble byte word pointer accumulator rest) =
      some (squareTopState template (advancePC 14 pc) base modulus nibble
        byte word pointer accumulator
        (WindowMath.squareWordAfter modulus 4 accumulator) rest) := by
  rw [fourSquareProgram, runInstructions_append, runInstructions_append,
    runInstructions_append, runInstructions_append,
    run_prepareSquare template pc base modulus nibble byte word pointer
      accumulator rest hrest]
  simp only [Option.bind_some]
  have hs0 := run_cachedSquare template (advancePC 6 pc) base modulus nibble
    byte word pointer accumulator accumulator [modulus, modulus, modulus, modulus] rest hrest (by simp)
  rw [hs0]
  simp only [Option.bind_some]
  have hs1 := run_cachedSquare template (advancePC 2 (advancePC 6 pc)) base modulus nibble
    byte word pointer accumulator (UInt256.mulMod accumulator accumulator modulus) [modulus, modulus, modulus] rest hrest (by simp)
  rw [hs1]
  simp only [Option.bind_some]
  have hs2 := run_cachedSquare template (advancePC 2 (advancePC 2 (advancePC 6 pc))) base modulus nibble
    byte word pointer accumulator (UInt256.mulMod (UInt256.mulMod accumulator accumulator modulus) (UInt256.mulMod accumulator accumulator modulus) modulus) [modulus, modulus] rest hrest (by simp)
  rw [hs2]
  simp only [Option.bind_some]
  have hs3 := run_cachedSquare template (advancePC 2 (advancePC 2 (advancePC 2 (advancePC 6 pc)))) base modulus nibble
    byte word pointer accumulator (UInt256.mulMod (UInt256.mulMod (UInt256.mulMod accumulator accumulator modulus) (UInt256.mulMod accumulator accumulator modulus) modulus) (UInt256.mulMod (UInt256.mulMod accumulator accumulator modulus) (UInt256.mulMod accumulator accumulator modulus) modulus) modulus) [modulus] rest hrest (by simp)
  rw [hs3]
  rfl

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
