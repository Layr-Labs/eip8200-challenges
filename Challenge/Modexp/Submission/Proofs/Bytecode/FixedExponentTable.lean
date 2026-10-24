import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentLoop
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace HistoricalSearch.FixedExponentTable
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel FixedExponentBlocks

theorem read_store_diff (mem : ByteArray) (word : UInt256) (i j : Nat) (hd : j+32 ≤ i ∨ i+32 ≤ j) :
    MachineState.readWord (WindowTableMemory.storeWord mem i word) j =
      MachineState.readWord mem j := by
  unfold WindowTableMemory.storeWord
  apply Challenge.EvmProof.Memory.readWord_writeBytes_disjoint
  simp only [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  exact hd

def power0 (base modulus : UInt256) : UInt256 := base
def power1 (base modulus : UInt256) : UInt256 := UInt256.mulMod base base modulus
def power2 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power0 base modulus) (power1 base modulus) modulus
def power3 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power1 base modulus) (power2 base modulus) modulus
def power4 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power1 base modulus) (power3 base modulus) modulus
def power5 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power1 base modulus) (power4 base modulus) modulus
def power6 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power1 base modulus) (power5 base modulus) modulus
def power7 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power1 base modulus) (power6 base modulus) modulus
def power8 (base modulus : UInt256) : UInt256 := UInt256.mulMod (power1 base modulus) (power7 base modulus) modulus

def memory0 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord ByteArray.empty 0 base
def memory1 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory0 base modulus) 32 (power1 base modulus)
def memory2 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory1 base modulus) 64 (power2 base modulus)
def memory3 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory2 base modulus) 96 (power3 base modulus)
def memory4 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory3 base modulus) 128 (power4 base modulus)
def memory5 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory4 base modulus) 160 (power5 base modulus)
def memory6 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory5 base modulus) 192 (power6 base modulus)
def memory7 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory6 base modulus) 224 (power7 base modulus)
def memory8 (base modulus : UInt256) : ByteArray := WindowTableMemory.storeWord (memory7 base modulus) 32 (power8 base modulus)

def table (base modulus : UInt256) : Nat → UInt256
  | 0 => base
  | 1 => power8 base modulus
  | 2 => power2 base modulus
  | 3 => power3 base modulus
  | 4 => power4 base modulus
  | 5 => power5 base modulus
  | 6 => power6 base modulus
  | 7 => power7 base modulus
  | _ => 0

theorem read_table (base modulus : UInt256) (slot : Nat) (hslot : slot < 8) :
    MachineState.readWord (memory8 base modulus) (32*slot) = table base modulus slot := by
  interval_cases slot <;>
    simp (disch := omega) [table, memory8,memory7,memory6,memory5,memory4,memory3,memory2,memory1,memory0,
      read_store_diff,WindowTableMemory.readWord_storeWord]

def cell1 : List Instr := WindowTwentyOneStage.pairProgram ++ saveProgram 1
theorem run_cell1 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell1
      (framed template pc (memory0 base modulus) 1
        (power0 base modulus :: List.replicate (count+8) modulus ++ tail)) =
    some (framed template (advancePC 6 pc) (memory1 base modulus) 2
      (power1 base modulus :: List.replicate (count+7) modulus ++ tail)) := by
  have ha := run_square template pc (memory0 base modulus) 1 (power0 base modulus) modulus
    (List.replicate (count+7) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have hb := run_save template (advancePC 2 pc) (memory0 base modulus) 1 1
    (by decide) (by decide) (power1 base modulus)
    (List.replicate (count+7) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (WindowTwentyOneStage.pairProgram)
      (framed template pc (memory0 base modulus) 1
        (power0 base modulus :: List.replicate (count+8) modulus ++ tail)) =
    some (framed template (advancePC 2 pc) (memory0 base modulus) 1
      (power1 base modulus :: List.replicate (count+7) modulus ++ tail)) := by
    simpa [power1,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell1,memory1,slotSize,←advancePC_add] using hab

def cell2 : List Instr := FixedExponentBlocks.lookupProgram 0 ++ saveProgram 2
theorem run_cell2 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell2
      (framed template pc (memory1 base modulus) 2
        (power1 base modulus :: List.replicate (count+7) modulus ++ tail)) =
    some (framed template (advancePC 7 pc) (memory2 base modulus) 3
      (power2 base modulus :: List.replicate (count+6) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory1 base modulus) 0 = power0 base modulus := by
    simp (disch := omega) [memory0,memory1,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory1 base modulus) 2 0
    (by decide) (by decide) (power1 base modulus) modulus (power0 base modulus)
    (List.replicate (count+6) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 3 pc) (memory1 base modulus) 2 2
    (by decide) (by decide) (power2 base modulus)
    (List.replicate (count+6) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 0)
      (framed template pc (memory1 base modulus) 2
        (power1 base modulus :: List.replicate (count+7) modulus ++ tail)) =
    some (framed template (advancePC 3 pc) (memory1 base modulus) 2
      (power2 base modulus :: List.replicate (count+6) modulus ++ tail)) := by
    simpa [power2,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell2,memory2,slotSize,←advancePC_add] using hab

def cell3 : List Instr := FixedExponentBlocks.lookupProgram 1 ++ saveProgram 3
theorem run_cell3 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell3
      (framed template pc (memory2 base modulus) 3
        (power2 base modulus :: List.replicate (count+6) modulus ++ tail)) =
    some (framed template (advancePC 8 pc) (memory3 base modulus) 4
      (power3 base modulus :: List.replicate (count+5) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory2 base modulus) 32 = power1 base modulus := by
    simp (disch := omega) [memory0,memory1,memory2,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory2 base modulus) 3 1
    (by decide) (by decide) (power2 base modulus) modulus (power1 base modulus)
    (List.replicate (count+5) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 4 pc) (memory2 base modulus) 3 3
    (by decide) (by decide) (power3 base modulus)
    (List.replicate (count+5) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 1)
      (framed template pc (memory2 base modulus) 3
        (power2 base modulus :: List.replicate (count+6) modulus ++ tail)) =
    some (framed template (advancePC 4 pc) (memory2 base modulus) 3
      (power3 base modulus :: List.replicate (count+5) modulus ++ tail)) := by
    simpa [power3,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell3,memory3,slotSize,←advancePC_add] using hab

def cell4 : List Instr := FixedExponentBlocks.lookupProgram 1 ++ saveProgram 4
theorem run_cell4 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell4
      (framed template pc (memory3 base modulus) 4
        (power3 base modulus :: List.replicate (count+5) modulus ++ tail)) =
    some (framed template (advancePC 8 pc) (memory4 base modulus) 5
      (power4 base modulus :: List.replicate (count+4) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory3 base modulus) 32 = power1 base modulus := by
    simp (disch := omega) [memory0,memory1,memory2,memory3,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory3 base modulus) 4 1
    (by decide) (by decide) (power3 base modulus) modulus (power1 base modulus)
    (List.replicate (count+4) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 4 pc) (memory3 base modulus) 4 4
    (by decide) (by decide) (power4 base modulus)
    (List.replicate (count+4) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 1)
      (framed template pc (memory3 base modulus) 4
        (power3 base modulus :: List.replicate (count+5) modulus ++ tail)) =
    some (framed template (advancePC 4 pc) (memory3 base modulus) 4
      (power4 base modulus :: List.replicate (count+4) modulus ++ tail)) := by
    simpa [power4,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell4,memory4,slotSize,←advancePC_add] using hab

def cell5 : List Instr := FixedExponentBlocks.lookupProgram 1 ++ saveProgram 5
theorem run_cell5 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell5
      (framed template pc (memory4 base modulus) 5
        (power4 base modulus :: List.replicate (count+4) modulus ++ tail)) =
    some (framed template (advancePC 8 pc) (memory5 base modulus) 6
      (power5 base modulus :: List.replicate (count+3) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory4 base modulus) 32 = power1 base modulus := by
    simp (disch := omega) [memory0,memory1,memory2,memory3,memory4,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory4 base modulus) 5 1
    (by decide) (by decide) (power4 base modulus) modulus (power1 base modulus)
    (List.replicate (count+3) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 4 pc) (memory4 base modulus) 5 5
    (by decide) (by decide) (power5 base modulus)
    (List.replicate (count+3) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 1)
      (framed template pc (memory4 base modulus) 5
        (power4 base modulus :: List.replicate (count+4) modulus ++ tail)) =
    some (framed template (advancePC 4 pc) (memory4 base modulus) 5
      (power5 base modulus :: List.replicate (count+3) modulus ++ tail)) := by
    simpa [power5,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell5,memory5,slotSize,←advancePC_add] using hab

def cell6 : List Instr := FixedExponentBlocks.lookupProgram 1 ++ saveProgram 6
theorem run_cell6 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell6
      (framed template pc (memory5 base modulus) 6
        (power5 base modulus :: List.replicate (count+3) modulus ++ tail)) =
    some (framed template (advancePC 8 pc) (memory6 base modulus) 7
      (power6 base modulus :: List.replicate (count+2) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory5 base modulus) 32 = power1 base modulus := by
    simp (disch := omega) [memory0,memory1,memory2,memory3,memory4,memory5,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory5 base modulus) 6 1
    (by decide) (by decide) (power5 base modulus) modulus (power1 base modulus)
    (List.replicate (count+2) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 4 pc) (memory5 base modulus) 6 6
    (by decide) (by decide) (power6 base modulus)
    (List.replicate (count+2) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 1)
      (framed template pc (memory5 base modulus) 6
        (power5 base modulus :: List.replicate (count+3) modulus ++ tail)) =
    some (framed template (advancePC 4 pc) (memory5 base modulus) 6
      (power6 base modulus :: List.replicate (count+2) modulus ++ tail)) := by
    simpa [power6,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell6,memory6,slotSize,←advancePC_add] using hab

def cell7 : List Instr := FixedExponentBlocks.lookupProgram 1 ++ saveProgram 7
theorem run_cell7 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell7
      (framed template pc (memory6 base modulus) 7
        (power6 base modulus :: List.replicate (count+2) modulus ++ tail)) =
    some (framed template (advancePC 8 pc) (memory7 base modulus) 8
      (power7 base modulus :: List.replicate (count+1) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory6 base modulus) 32 = power1 base modulus := by
    simp (disch := omega) [memory0,memory1,memory2,memory3,memory4,memory5,memory6,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory6 base modulus) 7 1
    (by decide) (by decide) (power6 base modulus) modulus (power1 base modulus)
    (List.replicate (count+1) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 4 pc) (memory6 base modulus) 7 7
    (by decide) (by decide) (power7 base modulus)
    (List.replicate (count+1) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 1)
      (framed template pc (memory6 base modulus) 7
        (power6 base modulus :: List.replicate (count+2) modulus ++ tail)) =
    some (framed template (advancePC 4 pc) (memory6 base modulus) 7
      (power7 base modulus :: List.replicate (count+1) modulus ++ tail)) := by
    simpa [power7,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell7,memory7,slotSize,←advancePC_add] using hab

def cell8 : List Instr := FixedExponentBlocks.lookupProgram 1 ++ saveProgram 1
theorem run_cell8 (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions cell8
      (framed template pc (memory7 base modulus) 8
        (power7 base modulus :: List.replicate (count+1) modulus ++ tail)) =
    some (framed template (advancePC 8 pc) (memory8 base modulus) 8
      (power8 base modulus :: List.replicate (count+0) modulus ++ tail)) := by
  have hr : MachineState.readWord (memory7 base modulus) 32 = power1 base modulus := by
    simp (disch := omega) [memory0,memory1,memory2,memory3,memory4,memory5,memory6,memory7,power0,read_store_diff,WindowTableMemory.readWord_storeWord]
  have ha := run_lookup template pc (memory7 base modulus) 8 1
    (by decide) (by decide) (power7 base modulus) modulus (power1 base modulus)
    (List.replicate (count+0) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega) hr
  have hb := run_save template (advancePC 4 pc) (memory7 base modulus) 8 1
    (by decide) (by decide) (power8 base modulus)
    (List.replicate (count+0) modulus ++ tail)
    (by simp only [List.length_append,List.length_replicate]; omega)
  have ha' : runInstructions (FixedExponentBlocks.lookupProgram 1)
      (framed template pc (memory7 base modulus) 8
        (power7 base modulus :: List.replicate (count+1) modulus ++ tail)) =
    some (framed template (advancePC 4 pc) (memory7 base modulus) 8
      (power8 base modulus :: List.replicate (count+0) modulus ++ tail)) := by
    simpa [power8,power0,List.replicate_succ,List.cons_append,slotSize] using ha
  have hab := runInstructions_append_some _ _ _ _ _ ha' hb
  simpa [cell8,memory8,slotSize,←advancePC_add] using hab

def program : List Instr := cell1 ++ cell2 ++ cell3 ++ cell4 ++ cell5 ++ cell6 ++ cell7 ++ cell8

theorem run_program (template : State) (pc base modulus : UInt256)
    (count : Nat) (tail : List UInt256) (hcap : tail.length+count+12 < 1024) :
    runInstructions program
      (framed template pc (memory0 base modulus) 1
        (base :: List.replicate (count+8) modulus ++ tail)) =
    some (framed template (advancePC 61 pc) (memory8 base modulus) 8
      (power8 base modulus :: List.replicate count modulus ++ tail)) := by
  have h1 := run_cell1 template (advancePC 0 pc) base modulus count tail hcap
  have hprefix1 := h1
  have h2 := run_cell2 template (advancePC 6 pc) base modulus count tail hcap
  have hprefix2 := runInstructions_append_some _ _ _ _ _ hprefix1 h2
  have h3 := run_cell3 template (advancePC 13 pc) base modulus count tail hcap
  have hprefix3 := runInstructions_append_some _ _ _ _ _ hprefix2 h3
  have h4 := run_cell4 template (advancePC 21 pc) base modulus count tail hcap
  have hprefix4 := runInstructions_append_some _ _ _ _ _ hprefix3 h4
  have h5 := run_cell5 template (advancePC 29 pc) base modulus count tail hcap
  have hprefix5 := runInstructions_append_some _ _ _ _ _ hprefix4 h5
  have h6 := run_cell6 template (advancePC 37 pc) base modulus count tail hcap
  have hprefix6 := runInstructions_append_some _ _ _ _ _ hprefix5 h6
  have h7 := run_cell7 template (advancePC 45 pc) base modulus count tail hcap
  have hprefix7 := runInstructions_append_some _ _ _ _ _ hprefix6 h7
  have h8 := run_cell8 template (advancePC 53 pc) base modulus count tail hcap
  have hprefix8 := runInstructions_append_some _ _ _ _ _ hprefix7 h8
  simpa only [program,power0,←advancePC_add,advancePC,Nat.add_zero,List.append_assoc] using hprefix8

#print axioms run_program
end HistoricalSearch.FixedExponentTable
