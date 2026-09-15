import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true

/-! Shared MAC execution for the immediate-address kernel, split before
symbolic words grow. The selected loops share the pointer-free `L2` product
and early-store suffix. Legacy helper APIs remain available. -/

namespace Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode WindowNibbleKernel
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

theorem pc_add_add (pc : UInt256) (a b : Nat) :
    pc + UInt256.ofNat a + UInt256.ofNat b = pc + UInt256.ofNat (a + b) := by
  rw [word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-! ## First loop: stack `[maxWord, x, pa, c, y]` -/

namespace L1

def multiplyProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨5, by decide⟩), .op .MULMOD]

def borrowProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB]

def carryProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩),
   .op .GT, .op .SUB, .op .SUB]

def loadProgram (t : UInt256) : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 2 t, .op .MLOAD]

def sumProgram : List Instr :=
  [.op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .ADD, .op (.Swap ⟨1, by decide⟩)]

def productProgram : List Instr := (multiplyProgram ++ borrowProgram) ++ carryProgram
def accumulateProgram (t : UInt256) : List Instr := loadProgram t ++ sumProgram
def program (t : UInt256) : List Instr := productProgram ++ accumulateProgram t

theorem run_multiply (template : State) (pc x y c pa : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024) :
    runInstructions multiplyProgram
      (framed template pc ([maxWord, x, pa, c, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([UInt256.mulMod y x maxWord, x * y, pa, c, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, multiplyProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc5, hc6, List.exchange]

theorem run_borrow (template : State) (pc hi lo y c pa : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024) :
    runInstructions borrowProgram
      (framed template pc ([hi, lo, pa, c, y] ++ rest)) =
    some (framed template (advancePC 4 pc)
      ([UInt256.lt hi lo - hi, lo, pa, c, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, borrowProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc5, hc6]

theorem run_carry (template : State) (pc borrow lo y c pa : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024) :
    runInstructions carryProgram
      (framed template pc ([borrow, lo, pa, c, y] ++ rest)) =
    some (framed template (advancePC 8 pc)
      ([(UInt256.gt c (lo + c) - borrow) - lo, pa, lo + c, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, carryProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc5, hc6, List.exchange]

theorem run_product (template : State) (pc x y c pa : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024) :
    runInstructions productProgram
      (framed template pc ([maxWord, x, pa, c, y] ++ rest)) =
    some (framed template (advancePC 18 pc)
      ([partialCarry x y c, pa, x * y + c, y] ++ rest)) := by
  have hm := run_multiply template pc x y c pa rest hrest
  have hb := run_borrow template (advancePC 6 pc)
    (UInt256.mulMod y x maxWord) (x*y) y c pa rest hrest
  have hc := run_carry template (advancePC 4 (advancePC 6 pc))
    (UInt256.lt (UInt256.mulMod y x maxWord) (x*y) - UInt256.mulMod y x maxWord)
    (x*y) y c pa rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hm hb
  simpa only [productProgram, advancePC, partialCarry] using
    runInstructions_append_some _ _ _ _ _ both hc

theorem run_load (template : State) (pc part sum y pa t : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (loadProgram t)
      (framed template pc ([part, pa, sum, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([MachineState.readWord template.memory t.toNat, sum, part, pa, sum, y] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc4, hc5, hc6, State.activeWordsAfterUInt256, hactive, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_sum (template : State) (pc t sum part y pa : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024) :
    runInstructions sumProgram
      (framed template pc ([t, sum, part, pa, sum, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([t + sum, pa, UInt256.gt sum (t + sum) + part, y] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, sumProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc4, hc5, hc6, List.exchange]

theorem run_accumulate (template : State) (pc x y c pa t : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (accumulateProgram t)
      (framed template pc ([partialCarry x y c, pa, x * y + c, y] ++ rest)) =
    some (framed template (advancePC 6 (pc + UInt256.ofNat 5))
      ([macSum x y (MachineState.readWord template.memory t.toNat) c, pa,
        macCarry x y (MachineState.readWord template.memory t.toNat) c, y] ++ rest)) := by
  have hl := run_load template pc (partialCarry x y c) (x*y+c) y pa t rest hrest hactive
  have hs := run_sum template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory t.toNat) (x*y+c) (partialCarry x y c)
    y pa rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  rw [carry_eq, sum_eq] at both
  simpa only [accumulateProgram] using both

theorem run_mac (template : State) (pc x y c pa t : UInt256)
    (rest : List UInt256) (hrest : rest.length + 7 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (program t)
      (framed template pc ([maxWord, x, pa, c, y] ++ rest)) =
    some (framed template (advancePC 6 (advancePC 18 pc + UInt256.ofNat 5))
      ([macSum x y (MachineState.readWord template.memory t.toNat) c, pa,
        macCarry x y (MachineState.readWord template.memory t.toNat) c, y] ++ rest)) := by
  exact runInstructions_append_some _ _ _ _ _
    (run_product template pc x y c pa rest hrest)
    (run_accumulate template (advancePC 18 pc) x y c pa t rest hrest hactive)

end L1

/-! ## Second loop: stack `[maxWord, x, c, y]` -/

namespace L2

def multiplyProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨4, by decide⟩), .op .MULMOD]

def borrowProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB]

def carryProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨3, by decide⟩),
   .op .GT, .op .SUB, .op .SUB]

def loadProgram (t : UInt256) : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .push 2 t, .op .MLOAD]

def sumProgram : List Instr :=
  [.op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨2, by decide⟩),
   .op .GT, .op .ADD, .op (.Swap ⟨0, by decide⟩)]

def productProgram : List Instr := (multiplyProgram ++ borrowProgram) ++ carryProgram
def accumulateProgram (t : UInt256) : List Instr := loadProgram t ++ sumProgram
def program (t : UInt256) : List Instr := productProgram ++ accumulateProgram t

theorem run_multiply (template : State) (pc x y c : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions multiplyProgram
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([UInt256.mulMod y x maxWord, x * y, c, y] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, multiplyProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc4, hc5, List.exchange]

theorem run_borrow (template : State) (pc hi lo y c : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions borrowProgram
      (framed template pc ([hi, lo, c, y] ++ rest)) =
    some (framed template (advancePC 4 pc)
      ([UInt256.lt hi lo - hi, lo, c, y] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, borrowProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc4, hc5]

theorem run_carry (template : State) (pc borrow lo y c : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions carryProgram
      (framed template pc ([borrow, lo, c, y] ++ rest)) =
    some (framed template (advancePC 8 pc)
      ([(UInt256.gt c (lo + c) - borrow) - lo, lo + c, y] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, carryProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc4, hc5, List.exchange]

theorem run_product (template : State) (pc x y c : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions productProgram
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed template (advancePC 18 pc)
      ([partialCarry x y c, x * y + c, y] ++ rest)) := by
  have hm := run_multiply template pc x y c rest hrest
  have hb := run_borrow template (advancePC 6 pc)
    (UInt256.mulMod y x maxWord) (x*y) y c rest hrest
  have hc := run_carry template (advancePC 4 (advancePC 6 pc))
    (UInt256.lt (UInt256.mulMod y x maxWord) (x*y) - UInt256.mulMod y x maxWord)
    (x*y) y c rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hm hb
  simpa only [productProgram, advancePC, partialCarry] using
    runInstructions_append_some _ _ _ _ _ both hc

theorem run_load (template : State) (pc part sum y t : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (loadProgram t)
      (framed template pc ([part, sum, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 5)
      ([MachineState.readWord template.memory t.toNat, sum, part, sum, y] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc3, hc4, hc5, State.activeWordsAfterUInt256, hactive, succ_eq_add, word_add_assoc,
    Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_sum (template : State) (pc t sum part y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions sumProgram
      (framed template pc ([t, sum, part, sum, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([t + sum, UInt256.gt sum (t + sum) + part, y] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, sumProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc3, hc4, hc5, List.exchange]

theorem run_accumulate (template : State) (pc x y c t : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (accumulateProgram t)
      (framed template pc ([partialCarry x y c, x * y + c, y] ++ rest)) =
    some (framed template (advancePC 6 (pc + UInt256.ofNat 5))
      ([macSum x y (MachineState.readWord template.memory t.toNat) c,
        macCarry x y (MachineState.readWord template.memory t.toNat) c, y] ++ rest)) := by
  have hl := run_load template pc (partialCarry x y c) (x*y+c) y t rest hrest hactive
  have hs := run_sum template (pc + UInt256.ofNat 5)
    (MachineState.readWord template.memory t.toNat) (x*y+c) (partialCarry x y c)
    y rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  rw [carry_eq, sum_eq] at both
  simpa only [accumulateProgram] using both

theorem run_mac (template : State) (pc x y c t : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat t.toNat 32) = template.activeWords) :
    runInstructions (program t)
      (framed template pc ([maxWord, x, c, y] ++ rest)) =
    some (framed template (advancePC 6 (advancePC 18 pc + UInt256.ofNat 5))
      ([macSum x y (MachineState.readWord template.memory t.toNat) c,
        macCarry x y (MachineState.readWord template.memory t.toNat) c, y] ++ rest)) := by
  exact runInstructions_append_some _ _ _ _ _
    (run_product template pc x y c rest hrest)
    (run_accumulate template (advancePC 18 pc) x y c t rest hrest hactive)

/-! ## Zero incoming carry and shared early-store suffix -/

def zeroCarryProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩),
   .op .LT, .op .SUB, .op (.Dup ⟨1, by decide⟩), .op .ADD,
   .op (.Swap ⟨0, by decide⟩), .op (.Swap ⟨1, by decide⟩), .op .SUB]

def zeroProductProgram : List Instr := multiplyProgram ++ zeroCarryProgram

private opaque zero_carry_eq (borrow lo : UInt256) :
    UInt256.ofNat 0 - (lo + borrow) =
      (UInt256.gt (UInt256.ofNat 0) (lo + UInt256.ofNat 0) - borrow) - lo := by
  apply Challenge.EvmProof.Word.word_ext
  have hb : borrow.toNat < 2 ^ 256 := borrow.val.isLt
  have hl : lo.toNat < 2 ^ 256 := lo.val.isLt
  simp only [UInt256.gt, Challenge.EvmProof.Word.word_toNat_sub,
    Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.add_zero,
    Nat.not_lt_zero, ↓reduceIte]
  omega

theorem run_zero_carry (template : State) (pc hi lo y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions zeroCarryProgram
      (framed template pc ([hi, lo, UInt256.ofNat 0, y] ++ rest)) =
    some (framed template (advancePC 9 pc)
      ([UInt256.ofNat 0 - (lo + (UInt256.lt hi lo - hi)), lo, y] ++ rest)) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, zeroCarryProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc4, hc5, List.exchange]

/-- Only a cell whose incoming carry is zero may use this product schedule. -/
theorem run_product_zero (template : State) (pc x y : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024) :
    runInstructions zeroProductProgram
      (framed template pc ([maxWord, x, UInt256.ofNat 0, y] ++ rest)) =
    some (framed template (advancePC 15 pc)
      ([partialCarry x y (UInt256.ofNat 0), x * y + UInt256.ofNat 0, y] ++ rest)) := by
  have hm := run_multiply template pc x y (UInt256.ofNat 0) rest hrest
  have hc := run_zero_carry template (advancePC 6 pc)
    (UInt256.mulMod y x maxWord) (x*y) y rest hrest
  rw [zero_carry_eq] at hc
  have hz : x * y + UInt256.ofNat 0 = x * y := by
    apply Challenge.EvmProof.Word.word_ext
    simp only [Challenge.EvmProof.Word.word_toNat_add,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.zero_mod, Nat.add_zero]
    exact Nat.mod_eq_of_lt (x*y).val.isLt
  simpa only [zeroProductProgram, advancePC, partialCarry, hz] using
    runInstructions_append_some _ _ _ _ _ hm hc

def finishLoadProgram (tl : UInt256) : List Instr :=
  [.op (.Swap ⟨0, by decide⟩), .op (.Dup ⟨0, by decide⟩),
   .push 2 tl, .op .MLOAD, .op .ADD]

def finishStoreProgram (ts : UInt256) : List Instr :=
  [.op (.Dup ⟨0, by decide⟩), .push 2 ts, .op .MSTORE, .op .LT, .op .ADD]

def finishProgram (tl ts : UInt256) : List Instr :=
  finishLoadProgram tl ++ finishStoreProgram ts

theorem run_finish_load (template : State) (pc part sum y tl : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords) :
    runInstructions (finishLoadProgram tl)
      (framed template pc ([part, sum, y] ++ rest)) =
    some (framed template (pc + UInt256.ofNat 7)
      ([MachineState.readWord template.memory tl.toNat + sum, sum, part, y] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, finishLoadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc3, hc4, hc5, State.activeWordsAfterUInt256, hactive, List.exchange,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

theorem run_finish_store (template : State) (pc value sum part y ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (finishStoreProgram ts)
      (framed template pc ([value, sum, part, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded value.toNat 32) ts.toNat }
      (pc + UInt256.ofNat 7)
      ([UInt256.lt value sum + part, y] ++ rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [runInstructions, finishStoreProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    hc3, hc4, hc5, hrest, State.activeWordsAfterUInt256, hactive,
    succ_eq_add, word_add_assoc, Challenge.EvmProof.Word.ofNat_add_mod]

/-- Finish either loop without retaining a cursor or reading after the store. -/
theorem run_finish (template : State) (pc x y c tl ts : UInt256)
    (rest : List UInt256) (hrest : rest.length + 6 < 1024)
    (hload : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat tl.toNat 32) = template.activeWords)
    (hstore : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat ts.toNat 32) = template.activeWords) :
    runInstructions (finishProgram tl ts)
      (framed template pc ([partialCarry x y c, x * y + c, y] ++ rest)) =
    some (framed
      { template with
        memory := MachineState.writeBytes template.memory
          (Data.Bytes.natToBytesPadded
            (macSum x y (MachineState.readWord template.memory tl.toNat) c).toNat 32)
          ts.toNat }
      (pc + UInt256.ofNat 14)
      ([macCarry x y (MachineState.readWord template.memory tl.toNat) c, y] ++ rest)) := by
  have hl := run_finish_load template pc (partialCarry x y c) (x*y+c) y tl rest hrest hload
  have hs := run_finish_store template (pc + UInt256.ofNat 7)
    (MachineState.readWord template.memory tl.toNat + (x*y+c)) (x*y+c)
    (partialCarry x y c) y ts rest hrest hstore
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  have hcarry : UInt256.lt
      (MachineState.readWord template.memory tl.toNat + (x*y+c)) (x*y+c) +
      partialCarry x y c = macCarry x y (MachineState.readWord template.memory tl.toNat) c :=
    carry_eq x y (MachineState.readWord template.memory tl.toNat) c
  rw [hcarry, sum_eq] at both
  simpa only [finishProgram, pc_add_add] using both

end L2

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
