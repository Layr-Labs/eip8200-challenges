import Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

set_option warningAsError true
set_option maxHeartbeats 3000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

/-- The final low nibble has consumed both retained values. Byte and word
remain compatibility labels in this arbitrary-state certificate. -/
def finalLowNibbleState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := nibbleState template pc base modulus nibble byte word pointer accumulator rest
  { state with stack := [UInt256.ofNat nibble, pointer, accumulator, modulus] ++ rest }

def finalLowSquareTopState (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256) : State :=
  { finalLowNibbleState template pc base modulus nibble byte word pointer original rest with
    stack := [accumulator, UInt256.ofNat nibble, pointer, original, modulus] ++ rest }

/-- The final low product is the three-slot loop-advance result. -/
def finalLowResultState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := finalLowNibbleState template pc base modulus nibble byte word pointer accumulator rest
  { state with stack := [pointer, accumulator, modulus] ++ rest }

def finalLowBeginSquareProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def finalLowTopSquareProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Swap ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def finalLowFourSquareProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op (.Dup ⟨6, by decide⟩),
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩),
   .op .MULMOD]

def finalLowFusedSquareLookupProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 1 5, .op .SHL, .op .MLOAD, .op .MULMOD,
   .op (.Swap ⟨1, by decide⟩), .op .POP]

def finalLowSquareLookupProgram : List Instr :=
  finalLowFourSquareProgram ++ finalLowFusedSquareLookupProgram

set_option linter.unusedSimpArgs false in
private theorem run_finalLowBeginSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions finalLowBeginSquareProgram
      (finalLowNibbleState template pc base modulus nibble byte word pointer accumulator rest) =
    some (finalLowSquareTopState template (advancePC 4 pc) base modulus nibble byte word pointer
      accumulator (UInt256.mulMod accumulator accumulator modulus) rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, finalLowBeginSquareProgram, finalLowSquareTopState, finalLowNibbleState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h4, h5, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

set_option linter.unusedSimpArgs false in
private theorem run_finalLowTopSquare (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions finalLowTopSquareProgram
      (finalLowSquareTopState template pc base modulus nibble byte word pointer original accumulator rest) =
    some (finalLowSquareTopState template (advancePC 4 pc) base modulus nibble byte word pointer
      original (UInt256.mulMod accumulator accumulator modulus) rest) := by
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  simp (config := { maxSteps := 100000 }) (disch := omega)
    [runInstructions, finalLowTopSquareProgram, finalLowSquareTopState, finalLowNibbleState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h4, h5, h6, h7, h8, h9,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange, advancePC]

set_option linter.unusedSimpArgs false in
/-- The four pure squarings reduce in one pass to the five-slot square state
holding `squareWordAfter modulus 4 accumulator`: thirteen instructions, thirteen
bytes, peak depth ten plus `rest`. -/
theorem run_finalLowFourSquares (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) :
    runInstructions finalLowFourSquareProgram
      (finalLowNibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (finalLowSquareTopState template (advancePC 13 pc) base modulus nibble
        byte word pointer accumulator
        (WindowMath.squareWordAfter modulus 4 accumulator) rest) := by
  simpa only [finalLowFourSquareProgram, WindowSquareBatch.program4, WindowSquareBatch.stage4,
    WindowSquareBatch.pair, WindowSquareBatch.framed, finalLowNibbleState, finalLowSquareTopState, nibbleState,
    List.cons_append, List.nil_append] using
    WindowSquareBatch.run_batch4
      (finalLowNibbleState template pc base modulus nibble byte word pointer accumulator rest)
      pc (UInt256.ofNat nibble) pointer accumulator modulus rest hrest


set_option linter.unusedSimpArgs false in
/-- The fused block reduces on the square state (peak depth eight plus `rest`)
to the three-slot loop result, consuming the nibble and the external POP in one certificate. -/
theorem run_finalLowFusedSquareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer original accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions finalLowFusedSquareLookupProgram
      (finalLowSquareTopState template pc base modulus nibble byte word pointer
        original accumulator rest) =
      some (finalLowResultState template (advancePC 9 pc) base modulus nibble
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
  have h4 : rest.length + 1 + 1 + 1 + 1 < 1024 := by omega
  have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
  have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by
    omega
  simp (config := { maxSteps := 8000000 }) (disch := omega)
    [runInstructions, finalLowFusedSquareLookupProgram, finalLowSquareTopState, finalLowResultState, finalLowNibbleState, nibbleState,
      Challenge.EvmProof.Stepper.runInstr, hrest, h4, h5, h6, h7, h8, h9, h10,
      List.getElem?_cons_zero, List.getElem?_cons_succ, List.exchange,
      hshift, hoffset, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.literal_eq_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      advancePC]
  refine ⟨?_, mulMod_comm _ _ _⟩
  simp only [succ_eq_add,
    show UInt256.ofNat 20 = UInt256.ofNat 1 + UInt256.ofNat 19 by decide,
    show UInt256.ofNat 19 = UInt256.ofNat 1 + UInt256.ofNat 18 by decide,
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
whole program is twenty-one instructions in twenty-two bytes. -/
theorem run_finalLowSquareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions finalLowSquareLookupProgram
      (finalLowNibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (finalLowResultState template (advancePC 22 pc) base modulus nibble
        byte word pointer
        (WindowMath.nibbleWordStep modulus base accumulator nibble) rest) := by
  rw [finalLowSquareLookupProgram, runInstructions_append,
    run_finalLowFourSquares template pc base modulus nibble byte word pointer
      accumulator rest hrest]
  simp only [Option.bind_some]
  rw [run_finalLowFusedSquareLookup template (advancePC 13 pc) base modulus nibble
    byte word pointer accumulator (WindowMath.squareWordAfter modulus 4
      accumulator) rest hnibble hrest]
  rw [← advancePC_add]
  norm_num
  unfold WindowMath.nibbleWordStep
  rfl


/-- Final high nibble: the old calldata word is no longer retained. -/
def finalHighNibbleState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := nibbleState template pc base modulus nibble byte word pointer accumulator rest
  { state with stack := [UInt256.ofNat nibble, byte, pointer, accumulator, modulus] ++ rest }

def finalHighResultState (template : State) (pc : UInt256) (base modulus : UInt256)
    (nibble : Nat) (byte word pointer accumulator : UInt256)
    (rest : List UInt256) : State :=
  let state := finalHighNibbleState template pc base modulus nibble byte word pointer accumulator rest
  { state with stack := [byte, pointer, accumulator, modulus] ++ rest }

def finalHighFusedSquareLookupProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 15 5, .op .SHL, .op .MLOAD, .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩), .op .POP]

def finalHighSquareLookupProgram : List Instr :=
  lowFourSquareProgram ++ finalHighFusedSquareLookupProgram

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowNibbleKernel

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel

open EvmSemantics EvmSemantics.EVM YulEvmCompiler WindowNibbleKernel

/-- Actual final-byte endpoint: the calldata word is absent from the stack. -/
def finalWordKernelState (template : State) (pc : UInt256)
    (base modulus word pointer accumulator : UInt256) (rest : List UInt256) : State :=
  let state := wordKernelState template pc base modulus word pointer accumulator rest
  { state with stack := [pointer, accumulator, modulus] ++ rest }

def finalHighPrepProgram : List Instr :=
  [.push 1 3, .op .BYTE, .op (.Dup ⟨0, by decide⟩), .push 1 4, .op .SHR]

/-- Forty-nine instructions and eighty-six bytes, including the final
cleanup that formerly belonged to the loop-advance path. -/
def finalByteProgram : List Instr :=
  finalHighPrepProgram ++ finalHighSquareLookupProgram ++
    lowPrepProgram ++ finalLowSquareLookupProgram ++ finishProgram

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowByteKernel
