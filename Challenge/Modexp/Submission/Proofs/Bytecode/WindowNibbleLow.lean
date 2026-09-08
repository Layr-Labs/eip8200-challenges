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

def lowFourSquareProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨5, by decide⟩),
   .op (.Dup ⟨6, by decide⟩), .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨7, by decide⟩),
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD,
   .op (.Dup ⟨0, by decide⟩), .op .MULMOD]

def lowFusedSquareLookupProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Swap ⟨1, by decide⟩),
   .push 10 5, .op .SHL, .op .MLOAD, .op .MULMOD,
   .op (.Swap ⟨2, by decide⟩), .op .POP]

def lowSquareLookupProgram : List Instr :=
  lowFourSquareProgram ++ lowFusedSquareLookupProgram

private theorem run_lowStagedPair (template : State) (pc a m : UInt256)
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
/-- The four pure squarings reduce in one pass to the six-slot square state
holding `squareWordAfter modulus 4 accumulator`: thirteen instructions and
thirteen bytes. -/
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
  let start : State := lowNibbleState template pc base modulus nibble byte word pointer
    accumulator rest
  have stage : runInstructions (lowFourSquareProgram.take 5) start =
      some { start with
        pc := advancePC 5 pc
        stack := accumulator :: modulus :: modulus :: modulus :: modulus :: start.stack } := by
    have h5 : rest.length + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h6 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h7 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h8 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h9 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    have h10 : rest.length + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 1024 := by omega
    simp (config := { maxSteps := 100000 }) (disch := omega)
      [lowFourSquareProgram, runInstructions, start, lowNibbleState, nibbleState,
        Challenge.EvmProof.Stepper.runInstr, advancePC,
        h5, h6, h7, h8, h9, h10, List.getElem?_cons_zero, List.getElem?_cons_succ]
  let pair : List Instr := [.op (.Dup ⟨0, by decide⟩), .op .MULMOD]
  let a1 := UInt256.mulMod accumulator accumulator modulus
  let a2 := UInt256.mulMod a1 a1 modulus
  let a3 := UInt256.mulMod a2 a2 modulus
  have h1 := run_lowStagedPair start (advancePC 5 pc) accumulator modulus
    (modulus :: modulus :: modulus :: start.stack)
    (by simp [start, lowNibbleState]; omega)
  have h2 := run_lowStagedPair start (advancePC 2 (advancePC 5 pc)) a1 modulus
    (modulus :: modulus :: start.stack) (by simp [start, lowNibbleState]; omega)
  have h3 := run_lowStagedPair start (advancePC 2 (advancePC 2 (advancePC 5 pc)))
    a2 modulus (modulus :: start.stack) (by simp [start, lowNibbleState]; omega)
  have h4 := run_lowStagedPair start
    (advancePC 2 (advancePC 2 (advancePC 2 (advancePC 5 pc)))) a3 modulus
    start.stack (by simp [start, lowNibbleState]; omega)
  have h01 := runInstructions_append_some _ _ _ _ _ stage h1
  have h012 := runInstructions_append_some _ _ _ _ _ h01 h2
  have h0123 := runInstructions_append_some _ _ _ _ _ h012 h3
  have hall := runInstructions_append_some _ _ _ _ _ h0123 h4
  simpa only [lowFourSquareProgram, pair, start, a1, a2, a3, List.take,
    WindowMath.squareWordAfter, lowNibbleState, lowSquareTopState, nibbleState,
    ← advancePC_add, show 5 + 2 + 2 + 2 + 2 = 13 by decide,
    List.cons_append, List.nil_append] using hall


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
      some (lowResultState template (advancePC 18 pc) base modulus nibble
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
pass.  The byte stride is unchanged: `advancePC 31` advances by BYTES and the
whole program is twenty-one instructions in thirty-one bytes. -/
theorem run_lowSquareLookup (template : State) (pc : UInt256)
    (base modulus : UInt256) (nibble : Nat)
    (byte word pointer accumulator : UInt256) (rest : List UInt256)
    (hnibble : nibble < 16) (hrest : rest.length ≤ 1000) :
    runInstructions lowSquareLookupProgram
      (lowNibbleState template pc base modulus nibble byte word pointer
        accumulator rest) =
      some (lowResultState template (advancePC 31 pc) base modulus nibble
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
