import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentBlocks
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace HistoricalSearch.FixedExponentLoop
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel FixedExponentBlocks

abbrev Operation := Option Nat

def operationProgram : Operation → List Instr
  | none => WindowTwentyOneStage.pairProgram
  | some slot => lookupProgram slot

def operationSize : Operation → Nat
  | none => 2
  | some slot => slotSize slot

def operationValue (table : Nat → UInt256) (modulus : UInt256) : Operation → UInt256 → UInt256
  | none, acc => UInt256.mulMod acc acc modulus
  | some slot, acc => UInt256.mulMod (table slot) acc modulus

def program : List Operation → List Instr
  | [] => []
  | op :: ops => operationProgram op ++ program ops

def programSize : List Operation → Nat
  | [] => 0
  | op :: ops => operationSize op + programSize ops

def value (table : Nat → UInt256) (modulus : UInt256) : List Operation → UInt256 → UInt256
  | [], acc => acc
  | op :: ops, acc => value table modulus ops (operationValue table modulus op acc)

def Valid : List Operation → Prop
  | [] => True
  | none :: ops => Valid ops
  | some slot :: ops => slot < 8 ∧ Valid ops

theorem run_operation (template : State) (pc : UInt256) (mem : ByteArray)
    (table : Nat → UInt256) (hreads : ∀ slot, slot < 8 → MachineState.readWord mem (32*slot) = table slot)
    (modulus acc : UInt256) (op : Operation) (hvalid : ∀ slot, op = some slot → slot < 8)
    (tail : List UInt256) (hcap : tail.length+3 < 1024) :
    runInstructions (operationProgram op) (framed template pc mem 8 (acc :: modulus :: tail)) =
      some (framed template (advancePC (operationSize op) pc) mem 8
        (operationValue table modulus op acc :: tail)) := by
  cases op with
  | none => exact run_square template pc mem 8 acc modulus tail hcap
  | some slot =>
    exact run_lookup template pc mem 8 slot (by decide) (hvalid slot rfl)
      acc modulus (table slot) tail hcap (hreads slot (hvalid slot rfl))

theorem run_program (template : State) (pc : UInt256) (mem : ByteArray)
    (table : Nat → UInt256) (hreads : ∀ slot, slot < 8 → MachineState.readWord mem (32*slot) = table slot)
    (modulus acc : UInt256) (ops : List Operation) (hvalid : Valid ops)
    (tail : List UInt256) (hcap : tail.length + ops.length + 3 < 1024) :
    runInstructions (program ops)
      (framed template pc mem 8 (acc :: List.replicate ops.length modulus ++ tail)) =
      some (framed template (advancePC (programSize ops) pc) mem 8
        (value table modulus ops acc :: tail)) := by
  induction ops generalizing pc acc with
  | nil => rfl
  | cons op ops ih =>
    have hvop : ∀ slot, op = some slot → slot < 8 := by
      intro slot heq; subst op; exact hvalid.1
    have hvs : Valid ops := by cases op <;> simp_all [Valid]
    have hs := run_operation template pc mem table hreads modulus acc op hvop
      (List.replicate ops.length modulus ++ tail)
      (by simp only [List.length_append,List.length_replicate]; simp only [List.length_cons] at hcap; omega)
    have ht := ih (advancePC (operationSize op) pc) (operationValue table modulus op acc) hvs
      (by simp only [List.length_cons] at hcap; omega)
    have hall := runInstructions_append_some _ _ _ _ _ hs ht
    simpa only [program,programSize,value,List.length_cons,List.replicate_succ,
      List.cons_append,←advancePC_add] using hall

end HistoricalSearch.FixedExponentLoop
