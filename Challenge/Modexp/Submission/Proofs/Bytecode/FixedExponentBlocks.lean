import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneStage
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneReturn
import Challenge.Modexp.Submission.Proofs.Bytecode.FixedExponentMath

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace HistoricalSearch.FixedExponentBlocks
open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open WindowNibbleKernel

def framed (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (stack : List UInt256) : State :=
  { template with pc := pc, stack := stack, memory := mem, activeWords := UInt256.ofNat active }

def pushSlot (slot : Nat) : Instr :=
  .push (if slot = 0 then 0 else 1) (UInt256.ofNat (32 * slot))
def lookupProgram (slot : Nat) : List Instr := [pushSlot slot, .op .MLOAD, .op .MULMOD]
def saveProgram (slot : Nat) : List Instr := [.op (.Dup ⟨0, by decide⟩), pushSlot slot, .op .MSTORE]
def slotSize (slot : Nat) : Nat := if slot = 0 then 3 else 4

theorem active_lookup (active slot : Nat) (h : slot < active) :
    MachineState.activeWordsAfter active (32*slot) 32 = active := by
  simp [MachineState.activeWordsAfter]
  omega

theorem active_save (active slot : Nat) :
    MachineState.activeWordsAfter active (32*slot) 32 = max active (slot+1) := by
  simp [MachineState.activeWordsAfter, Nat.add_div, Nat.mul_div_right]

theorem run_square (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (acc modulus : UInt256) (tail : List UInt256) (hcap : tail.length+3 < 1024) :
    runInstructions WindowTwentyOneStage.pairProgram
      (framed template pc mem active (acc :: modulus :: tail)) =
    some (framed template (advancePC 2 pc) mem active
      (UInt256.mulMod acc acc modulus :: tail)) := by
  have hcap2 : tail.length+2 < 1024 := by omega
  simp [runInstructions, WindowTwentyOneStage.pairProgram, framed,
    Challenge.EvmProof.Stepper.runInstr, hcap, hcap2, advancePC]

theorem run_lookup (template : State) (pc : UInt256) (mem : ByteArray)
    (active slot : Nat) (hactive : active ≤ 8) (hslot : slot < active)
    (acc modulus value : UInt256) (tail : List UInt256) (hcap : tail.length+3 < 1024)
    (hread : MachineState.readWord mem (32*slot) = value) :
    runInstructions (lookupProgram slot)
      (framed template pc mem active (acc :: modulus :: tail)) =
    some (framed template (advancePC (slotSize slot) pc) mem active
      (UInt256.mulMod value acc modulus :: tail)) := by
  have hcap2 : tail.length+2 < 1024 := by omega
  have hs : (UInt256.ofNat (32*slot)).toNat = 32*slot := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  have hread0 : slot=0 → MachineState.readWord mem 0 = value := by
    intro hz; simpa [hz] using hread
  by_cases hz : slot=0 <;>
    simp [lookupProgram, pushSlot, slotSize, hz, runInstructions, framed,
      Challenge.EvmProof.Stepper.runInstr, hcap, hcap2, hs, ha, hread, hzero, hread0,
      State.activeWordsAfterUInt256, active_lookup active slot hslot, MachineState.activeWordsAfter,
      advancePC, succ_eq_add, hp2, hp3, word_add_assoc] <;>
    apply congrArg UInt256.ofNat <;> exact Nat.max_eq_left (by omega)

theorem run_save (template : State) (pc : UInt256) (mem : ByteArray)
    (active slot : Nat) (hactive : active ≤ 8) (hslot : slot < 8)
    (acc : UInt256) (tail : List UInt256) (hcap : tail.length+3 < 1024) :
    runInstructions (saveProgram slot)
      (framed template pc mem active (acc :: tail)) =
    some (framed template (advancePC (slotSize slot) pc)
      (WindowTableMemory.storeWord mem (32*slot) acc) (max active (slot+1)) (acc :: tail)) := by
  have hc1 : tail.length+1 < 1024 := by omega
  have hc2 : tail.length+2 < 1024 := by omega
  have hs : (UInt256.ofNat (32*slot)).toNat = 32*slot := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hp2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hp3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hzero : ({ val := 0 } : UInt256).toNat = 0 := rfl
  by_cases hz : slot=0 <;>
    simp [saveProgram, pushSlot, slotSize, hz, runInstructions, framed,
      Challenge.EvmProof.Stepper.runInstr, hc1, hc2, hcap, hs, ha, hzero,
      WindowTableMemory.storeWord, State.activeWordsAfterUInt256, active_save, MachineState.activeWordsAfter,
      advancePC, succ_eq_add, hp2, hp3, word_add_assoc] <;>
    congr 1 <;> congr 1 <;> omega

#print axioms run_lookup
#print axioms run_save
end HistoricalSearch.FixedExponentBlocks
