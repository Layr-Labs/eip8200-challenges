import Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacWords

set_option warningAsError true

/-! Shared MAC execution for the immediate-address kernel, split before
symbolic words grow.  `L1` keeps the `a` cursor under the operands; `L2`
carries no pointer at all. -/

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

end L2

end Challenge.Modexp.Submission.Proofs.Fast.CiosCachedMacCore
