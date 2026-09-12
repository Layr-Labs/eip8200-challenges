import Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-- The low nibble has consumed its byte. The byte parameter is only a
compatibility label; it is absent from the five-slot machine stack. -/
def lowNibbleState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := nibbleState template pc base modulus nibble byte word pointer accumulator rest
  { state with stack := [UInt256.ofNat nibble, word, pointer, accumulator, modulus] ++ rest }

def lowSquareTopState (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256) : State :=
  { lowNibbleState template pc base modulus nibble byte word pointer original rest with
    stack := [accumulator, UInt256.ofNat nibble, word, pointer, original, modulus] ++ rest }

/-- The low product is already the four-slot word-kernel result. -/
def lowResultState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := lowNibbleState template pc base modulus nibble byte word pointer accumulator rest
  { state with stack := [word, pointer, accumulator, modulus] ++ rest }

def lowBeginSquareProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def lowTopSquareProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def lowFourSquareProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD]

def lowFusedSquareLookupProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 1 5, .op .SHL, .op .MLOAD, .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩), .op .POP]

def lowSquareLookupProgram : List Instr :=
  lowFourSquareProgram ++ lowFusedSquareLookupProgram

set_option linter.unusedSimpArgs false in
private theorem run_lowBeginSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions lowBeginSquareProgram
      (lowNibbleState template pc base modulus nibble byte word pointer accumulator rest) =
    some (lowSquareTopState template (advancePC 4 pc) base modulus nibble byte word pointer
      accumulator (UInt256.mulMod accumulator accumulator modulus) rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, lowBeginSquareProgram, lowSquareTopState, lowNibbleState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h5, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

set_option linter.unusedSimpArgs false in
private theorem run_lowTopSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions lowTopSquareProgram
      (lowSquareTopState template pc base modulus nibble byte word pointer original accumulator rest) =
    some (lowSquareTopState template (advancePC 4 pc) base modulus nibble byte word pointer
      original (UInt256.mulMod accumulator accumulator modulus) rest) := by
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, lowTopSquareProgram, lowSquareTopState, lowNibbleState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h5, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

set_option linter.unusedSimpArgs false in
/-- The four pure squarings reduce in one pass to the six-slot square state
holding `squareWordAfter modulus 4 accumulator`: thirteen instructions, thirteen
bytes, peak depth eleven plus `rest`. -/
theorem run_lowFourSquares (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions lowFourSquareProgram
      (lowNibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (lowSquareTopState template (advancePC 13 pc) base modulus nibble
        byte word pointer accumulator
        (WindowMath.squareWordAfter modulus 4 accumulator) rest) := by
  simpa only [lowFourSquareProgram, WindowSquareBatch.program5, WindowSquareBatch.stage5,
    WindowSquareBatch.pair, WindowSquareBatch.framed, lowNibbleState, lowSquareTopState, nibbleState,
    List.cons_append, List.nil_append] using
    WindowSquareBatch.run_batch5
      (lowNibbleState template pc base modulus nibble byte word pointer accumulator rest)
      pc (UInt256.ofNat nibble) word pointer accumulator modulus rest hrest


set_option linter.unusedSimpArgs false in
/-- The fused block reduces on the square state (peak depth nine plus `rest`)
to the four-slot word result, consuming the nibble and the external POP in one certificate. -/
theorem run_lowFusedSquareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions lowFusedSquareLookupProgram
      (lowSquareTopState template pc base modulus nibble byte word pointer
        original accumulator rest) =
      some (lowResultState template (advancePC 9 pc) base modulus nibble
        byte word pointer
        (UInt256.mulMod accumulator
          (WindowMath.tableWord base modulus nibble) modulus) rest) := by
  have hshift := shift_nibble nibble hnibble
  have hoffset : (UInt256.ofNat (32 * nibble)).toNat = 32 * nibble := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    apply Nat.mod_eq_of_lt
    omega
  have hread := WindowTableMemory.readWord_tableMemory base modulus nibble hnibble
  have hactive := WindowTableMemory.activeWordsAfter_lookup nibble hnibble
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 8000000 }) (disch := omega)
    [runInstructions, lowFusedSquareLookupProgram, lowSquareTopState, lowResultState, lowNibbleState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h5, h6, h7, h8, h9, h10,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      advancePC]
  refine ⟨?_, mulMod_comm _ _ _⟩
  simp only [succ_eq_add,
    show UInt256.ofNat 18 = UInt256.ofNat 1 + UInt256.ofNat 17 by decide,
    show UInt256.ofNat 17 = UInt256.ofNat 1 + UInt256.ofNat 16 by decide,
    show UInt256.ofNat 16 = UInt256.ofNat 1 + UInt256.ofNat 15 by decide,
    show UInt256.ofNat 15 = UInt256.ofNat 1 + UInt256.ofNat 14 by decide,
    show UInt256.ofNat 14 = UInt256.ofNat 1 + UInt256.ofNat 13 by decide,
    show UInt256.ofNat 13 = UInt256.ofNat 1 + UInt256.ofNat 12 by decide,
    show UInt256.ofNat 12 = UInt256.ofNat 1 + UInt256.ofNat 11 by decide,
    show UInt256.ofNat 11 = UInt256.ofNat 1 + UInt256.ofNat 10 by decide,
    show UInt256.ofNat 10 = UInt256.ofNat 1 + UInt256.ofNat 9 by decide,
    show UInt256.ofNat 9 = UInt256.ofNat 1 + UInt256.ofNat 8 by decide,
    show UInt256.ofNat 8 = UInt256.ofNat 1 + UInt256.ofNat 7 by decide,
    show UInt256.ofNat 7 = UInt256.ofNat 1 + UInt256.ofNat 6 by decide,
    show UInt256.ofNat 6 = UInt256.ofNat 1 + UInt256.ofNat 5 by decide,
    show UInt256.ofNat 5 = UInt256.ofNat 1 + UInt256.ofNat 4 by decide,
    show UInt256.ofNat 4 = UInt256.ofNat 1 + UInt256.ofNat 3 by decide,
    show UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 2 by decide,
    show UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 by decide,
    word_add_assoc]


set_option linter.unusedSimpArgs false in
/-- The square phase followed by the fused cleanup-and-lookup reduces in one
pass.  The compact byte stride is: `advancePC 22` advances by BYTES and the
whole program is twenty-one instructions in thirty-eight bytes. -/
theorem run_lowSquareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions lowSquareLookupProgram
      (lowNibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (lowResultState template (advancePC 22 pc) base modulus nibble
        byte word pointer
        (WindowMath.nibbleWordStep modulus base accumulator nibble) rest) := by
  rw [lowSquareLookupProgram, runInstructions_append,
    run_lowFourSquares template pc base modulus nibble byte word pointer
      accumulator rest hrest]
  simp only [Option.bind_some]
  rw [run_lowFusedSquareLookup template (advancePC 13 pc) base modulus nibble
    byte word pointer accumulator (WindowMath.squareWordAfter modulus 4
      accumulator) rest hnibble hrest]
  rw [← advancePC_add]
  norm_num
  unfold WindowMath.nibbleWordStep
  rfl


end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel
