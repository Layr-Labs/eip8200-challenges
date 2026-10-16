import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentTable
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 8000
set_option maxHeartbeats 3000000
namespace HistoricalSearch.FixedExponentProgram
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel FixedExponentBlocks

def initProgram : List Instr := [.op (.Dup ⟨2, by decide⟩), .push 0 0, .op .MSTORE]
def poolProgram : List Instr := List.replicate 305 (.op (.Dup ⟨0, by decide⟩))
def restoreProgram : List Instr := [.push 0 0, .op .MLOAD]
def operations : List FixedExponentLoop.Operation := [
  some 5, none, none, none, some 0, none, none, none, none, some 5, none, none,
  none, none, some 0, none, none, none, none, none, some 4, none, none, none,
  none, none, some 4, none, none, none, some 0, none, none, none, none, some 4,
  none, none, none, none, none, some 0, none, none, none, none, some 2, none,
  none, none, none, none, none, none, some 7, none, none, none, none, none,
  none, none, none, none, none, some 3, none, none, none, none, some 2, none,
  none, none, none, some 4, none, none, none, none, none, none, none, some 3,
  none, none, none, none, none, none, some 0, none, none, none, none, none,
  none, some 3, none, none, none, none, some 6, none, none, none, none, none,
  some 7, none, none, none, none, none, none, none, none, some 2, none, none,
  none, none, none, none, none, some 0, none, none, none, none, none, some 6,
  none, none, none, none, none, none, none, none, some 6, none, none, none,
  none, some 6, none, none, none, some 0, none, none, none, none, none, some 1,
  none, none, none, none, none, none, none, none, none, none, some 6, none,
  none, none, none, some 3, none, none, none, none, none, some 5, none, none,
  none, none, some 0, none, none, none, none, none, some 7, none, none, none,
  none, none, none, none, some 4, none, none, none, none, none, none, some 4,
  none, none, none, some 0, none, none, none, none, some 3, none, none, none,
  none, none, none, none, some 7, none, none, none, none, none, none, some 1,
  none, none, none, none, none, some 0, none, none, none, none, none, none,
  some 0, none, none, none, none, none, some 2, none, none, none, none, none,
  none, some 0, none, none, none, none, none, some 7, none, none, none, none,
  some 6, none, none, none, none, none, some 0, none, none, none, none, some 1,
  none, none, none, none, none, none, some 1, none, none, none, none, some 7,
  none, none, some 0, none, none, none, none, none, none, some 3
]

theorem operations_valid : FixedExponentLoop.Valid operations := by simp [operations,FixedExponentLoop.Valid]
theorem operations_length : operations.length = 298 := rfl
theorem operations_size : FixedExponentLoop.programSize operations = 680 := rfl

theorem arithmetic (base modulus : UInt256) :
    FixedExponentLoop.value (FixedExponentTable.table base modulus) modulus operations
      (FixedExponentTable.power8 base modulus) = FixedExponent.value base modulus := by
  rfl

def program : List Instr :=
  initProgram ++ poolProgram ++ restoreProgram ++ FixedExponentTable.program ++
    FixedExponentLoop.program operations ++ WindowTwentyOneReturn.program

theorem run_init (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 590) :
    runInstructions initProgram
      (framed template pc ByteArray.empty 0 ([modulus,exponent,base] ++ rest)) =
    some (framed template (advancePC 3 pc) (FixedExponentTable.memory0 base modulus) 1
      ([modulus,exponent,base] ++ rest)) := by
  have h3 : rest.length+3 < 1024 := by omega
  have h4 : rest.length+4 < 1024 := by omega
  have h5 : rest.length+5 < 1024 := by omega
  have hz : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (disch := omega) [initProgram,runInstructions,framed,FixedExponentTable.memory0,
    WindowTableMemory.storeWord,Challenge.EvmProof.Stepper.runInstr,h3,h4,h5,hz,List.getElem?_cons_zero,
    State.activeWordsAfterUInt256,MachineState.activeWordsAfter,advancePC]

theorem run_restore (template : State) (pc : UInt256) (mem : ByteArray)
    (base : UInt256) (stack : List UInt256) (hcap : stack.length+1 < 1024)
    (hread : MachineState.readWord mem 0 = base) :
    runInstructions restoreProgram (framed template pc mem 1 stack) =
    some (framed template (advancePC 2 pc) mem 1 (base :: stack)) := by
  have hz : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have h0 : stack.length < 1024 := by omega
  simp [restoreProgram,runInstructions,framed,Challenge.EvmProof.Stepper.runInstr,hcap,h0,hz,hread,
    State.activeWordsAfterUInt256,MachineState.activeWordsAfter,advancePC]

def resultTemplate (template : State) (base modulus : UInt256) : State :=
  { template with memory := FixedExponentTable.memory8 base modulus, activeWords := UInt256.ofNat 8 }

def finalState (template : State) (pc base modulus exponent : UInt256) (rest : List UInt256) : State :=
  WindowTwentyOneReturn.returned (resultTemplate template base modulus)
    (advancePC 1056 pc) (FixedExponent.value base modulus) 8 ([exponent,base] ++ rest)

theorem run_program (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 590) :
    runInstructions program
      (framed template pc ByteArray.empty 0 ([modulus,exponent,base] ++ rest)) =
    some (finalState template pc base modulus exponent rest) := by
  let tail := [exponent,base] ++ rest
  have hi := run_init template pc base modulus exponent rest hrest
  have hp := WindowTwentyOneStage.run_topCopies
    (framed template pc (FixedExponentTable.memory0 base modulus) 1 [])
    (advancePC 3 pc) modulus tail 305 (by simp [tail]; omega)
  have hp' : runInstructions poolProgram
      (framed template (advancePC 3 pc) (FixedExponentTable.memory0 base modulus) 1
        ([modulus,exponent,base] ++ rest)) =
    some (framed template (advancePC 308 pc) (FixedExponentTable.memory0 base modulus) 1
      (List.replicate 306 modulus ++ tail)) := by
    simpa [poolProgram,WindowTwentyOneStage.framed,framed,tail,←advancePC_add,List.cons_append] using hp
  have hl := run_restore template (advancePC 308 pc) (FixedExponentTable.memory0 base modulus) base
    (List.replicate 306 modulus ++ tail) (by simp [tail]; omega)
    (by exact WindowTableMemory.readWord_storeWord ByteArray.empty 0 base)
  have ht := FixedExponentTable.run_program template (advancePC 310 pc) base modulus 298 tail
    (by simp [tail]; omega)
  have he := FixedExponentLoop.run_program template (advancePC 371 pc)
    (FixedExponentTable.memory8 base modulus) (FixedExponentTable.table base modulus)
    (FixedExponentTable.read_table base modulus) modulus (FixedExponentTable.power8 base modulus)
    operations operations_valid tail (by rw [operations_length]; simp [tail]; omega)
  have hr := WindowTwentyOneReturn.run_return (resultTemplate template base modulus)
    (advancePC 1051 pc) (FixedExponent.value base modulus) 8 (by decide) rfl tail
    (by simp [tail]; omega)
  have hl' : runInstructions restoreProgram
      (framed template (advancePC 308 pc) (FixedExponentTable.memory0 base modulus) 1
        (List.replicate 306 modulus ++ tail)) =
    some (framed template (advancePC 310 pc) (FixedExponentTable.memory0 base modulus) 1
      (base :: List.replicate 306 modulus ++ tail)) := by
    simpa [←advancePC_add,List.cons_append] using hl
  have ht' : runInstructions FixedExponentTable.program
      (framed template (advancePC 310 pc) (FixedExponentTable.memory0 base modulus) 1
        (base :: List.replicate 306 modulus ++ tail)) =
    some (framed template (advancePC 371 pc) (FixedExponentTable.memory8 base modulus) 8
      (FixedExponentTable.power8 base modulus :: List.replicate 298 modulus ++ tail)) := by
    simpa only [←advancePC_add] using ht
  have he' : runInstructions (FixedExponentLoop.program operations)
      (framed template (advancePC 371 pc) (FixedExponentTable.memory8 base modulus) 8
        (FixedExponentTable.power8 base modulus :: List.replicate 298 modulus ++ tail)) =
    some (framed template (advancePC 1051 pc) (FixedExponentTable.memory8 base modulus) 8
      (FixedExponent.value base modulus :: tail)) := by
    simpa only [operations_length,operations_size,arithmetic,←advancePC_add] using he
  have hr' : runInstructions WindowTwentyOneReturn.program
      (framed template (advancePC 1051 pc) (FixedExponentTable.memory8 base modulus) 8
        (FixedExponent.value base modulus :: tail)) =
    some (finalState template pc base modulus exponent rest) := by
    simpa only [WindowTwentyOneReturn.framed,framed,resultTemplate,finalState,tail,←advancePC_add] using hr
  have hip := runInstructions_append_some _ _ _ _ _ hi hp'
  have hipl := runInstructions_append_some _ _ _ _ _ hip hl'
  have hiplt := runInstructions_append_some _ _ _ _ _ hipl ht'
  have hiplte := runInstructions_append_some _ _ _ _ _ hiplt he'
  have hall := runInstructions_append_some _ _ _ _ _ hiplte hr'
  simpa only [program,List.append_assoc] using hall

#print axioms run_program
end HistoricalSearch.FixedExponentProgram
