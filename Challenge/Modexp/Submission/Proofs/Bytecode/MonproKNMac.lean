import Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMacWords

set_option warningAsError true

/-! Shared cached MAC execution, split before symbolic words grow. -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel MonproKNCache
open Challenge.Modexp.Submission.Proofs.Fast.Monpro

def multiplyProgram : List Instr :=
  [.op (.Dup ⟨5, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .MUL,
   .op (.Swap ⟨1, by decide⟩), .op (.Dup ⟨6, by decide⟩), .op .MULMOD]

def borrowProgram : List Instr :=
  [.op (.Dup ⟨1, by decide⟩), .op (.Dup ⟨1, by decide⟩), .op .LT, .op .SUB]

def carryProgram : List Instr :=
  [.op (.Dup ⟨4, by decide⟩), .op (.Dup ⟨2, by decide⟩), .op .ADD,
   .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨5, by decide⟩),
   .op .GT, .op .SUB, .op .SUB]

def loadProgram : List Instr :=
  [.op (.Dup ⟨3, by decide⟩), .op (.Dup ⟨3, by decide⟩), .op .MLOAD]

def sumProgram : List Instr :=
  [.op .ADD, .op (.Dup ⟨0, by decide⟩), .op (.Swap ⟨4, by decide⟩),
   .op .GT, .op .ADD, .op (.Swap ⟨2, by decide⟩)]

def productProgram : List Instr := (multiplyProgram ++ borrowProgram) ++ carryProgram
def accumulateProgram : List Instr := loadProgram ++ sumProgram
def program : List Instr := productProgram ++ accumulateProgram

theorem run_multiply (template : State) (pc x y c pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions multiplyProgram
      (framed template pc ([maxWord, x, pa, pt, c, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([UInt256.mulMod y x maxWord, x * y, pa, pt, c, y] ++ rest)) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, multiplyProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc6, hc7, List.exchange]

theorem run_borrow (template : State) (pc hi lo y c pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions borrowProgram
      (framed template pc ([hi, lo, pa, pt, c, y] ++ rest)) =
    some (framed template (advancePC 4 pc)
      ([UInt256.lt hi lo - hi, lo, pa, pt, c, y] ++ rest)) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, borrowProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc6, hc7]

theorem run_carry (template : State) (pc borrow lo y c pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions carryProgram
      (framed template pc ([borrow, lo, pa, pt, c, y] ++ rest)) =
    some (framed template (advancePC 8 pc)
      ([(UInt256.gt c (lo + c) - borrow) - lo, pa, pt, lo + c, y] ++ rest)) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, carryProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hrest, hc6, hc7, List.exchange]

theorem run_product (template : State) (pc x y c pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions productProgram
      (framed template pc ([maxWord, x, pa, pt, c, y] ++ rest)) =
    some (framed template (advancePC 18 pc)
      ([partialCarry x y c, pa, pt, x * y + c, y] ++ rest)) := by
  have hm := run_multiply template pc x y c pa pt rest hrest
  have hb := run_borrow template (advancePC 6 pc)
    (UInt256.mulMod y x maxWord) (x*y) y c pa pt rest hrest
  have hc := run_carry template (advancePC 4 (advancePC 6 pc))
    (UInt256.lt (UInt256.mulMod y x maxWord) (x*y) - UInt256.mulMod y x maxWord)
    (x*y) y c pa pt rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hm hb
  simpa only [productProgram, advancePC, partialCarry] using
    runInstructions_append_some _ _ _ _ _ both hc

theorem run_load (template : State) (pc part sum y pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pt.toNat 32) = template.activeWords) :
    runInstructions loadProgram
      (framed template pc ([part, pa, pt, sum, y] ++ rest)) =
    some (framed template (advancePC 3 pc)
      ([MachineState.readWord template.memory pt.toNat, sum, part, pa, pt, sum, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, loadProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc5, hc6, hc7, State.activeWordsAfterUInt256, hactive]

theorem run_sum (template : State) (pc t sum part y pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024) :
    runInstructions sumProgram
      (framed template pc ([t, sum, part, pa, pt, sum, y] ++ rest)) =
    some (framed template (advancePC 6 pc)
      ([t + sum, pa, pt, UInt256.gt sum (t + sum) + part, y] ++ rest)) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  simp [runInstructions, sumProgram, framed, Challenge.EvmProof.Stepper.runInstr,
    advancePC, hc5, hc6, hc7, List.exchange]

theorem run_accumulate (template : State) (pc x y c pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pt.toNat 32) = template.activeWords) :
    runInstructions accumulateProgram
      (framed template pc ([partialCarry x y c, pa, pt, x * y + c, y] ++ rest)) =
    some (framed template (advancePC 9 pc)
      ([macSum x y (MachineState.readWord template.memory pt.toNat) c, pa, pt,
        macCarry x y (MachineState.readWord template.memory pt.toNat) c, y] ++ rest)) := by
  have hl := run_load template pc (partialCarry x y c) (x*y+c) y pa pt rest hrest hactive
  have hs := run_sum template (advancePC 3 pc)
    (MachineState.readWord template.memory pt.toNat) (x*y+c) (partialCarry x y c)
    y pa pt rest hrest
  have both := runInstructions_append_some _ _ _ _ _ hl hs
  rw [carry_eq, sum_eq] at both
  simpa only [accumulateProgram, advancePC] using both

theorem run_mac (template : State) (pc x y c pa pt : UInt256)
    (rest : List UInt256) (hrest : rest.length + 8 < 1024)
    (hactive : UInt256.ofNat (MachineState.activeWordsAfter
      template.activeWords.toNat pt.toNat 32) = template.activeWords) :
    runInstructions program
      (framed template pc ([maxWord, x, pa, pt, c, y] ++ rest)) =
    some (framed template (advancePC 9 (advancePC 18 pc))
      ([macSum x y (MachineState.readWord template.memory pt.toNat) c, pa, pt,
        macCarry x y (MachineState.readWord template.memory pt.toNat) c, y] ++ rest)) := by
  exact runInstructions_append_some _ _ _ _ _
    (run_product template pc x y c pa pt rest hrest)
    (run_accumulate template (advancePC 18 pc) x y c pa pt rest hrest hactive)

end Challenge.Modexp.Submission.Proofs.Bytecode.MonproKNMac
