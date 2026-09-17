import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowCopyMemory
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

/-!
The first exponent-copy setup starts with exactly sixteen active words.
The frontier is 512 before the first MSTORE and 544 before the second.
This specialization must not replace the continuing-pass stores, which
start with eighteen active words. No table-value, exponent, or modulus
restriction is required. MSIZE is interpreted by the existing, sound
submission-local extended evaluator, not the protected runInstr.
-/
namespace Challenge.Modexp.Submission.Proofs.Bytecode.FrontierFirstCopy

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

/-- Eight instructions / thirteen bytes. PUSH5 only retains the old span. -/
def tailProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 5 4, .op .SHR, .op .MSIZE, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .MSIZE, .op .MSTORE]

def storesProgram : List Instr := tailProgram ++ WindowTwentyOneStage.stageHead

/-- Exact same complete output state as the old setup at active = 16. -/
theorem run_tail (template : State) (pc : UInt256) (mem : ByteArray)
    (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX tailProgram
      (WindowTwentyOneGroup.state template pc mem 16 modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneLookup.framed template (advancePC 13 pc)
      (WindowCopyMemory.copyMem mem exponent) 18
      ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest)) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have h16 : (UInt256.ofNat 16).toNat = 16 := rfl
  have h17 : (UInt256.ofNat 17).toNat = 17 := rfl
  have h512 : (UInt256.ofNat 512).toNat = 512 := rfl
  have h544 : (UInt256.ofNat 544).toNat = 544 := rfl
  have hfirst : MachineState.activeWordsAfter 16 512 32 = 17 := by decide
  have hsecond : MachineState.activeWordsAfter 17 544 32 = 18 := by decide
  have hpush6 : UInt256.ofNat 6 =
      UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
      UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructionsX, runInstrX, tailProgram,
    WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    WindowCopyMemory.copyMem, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap5, hcap6, hcap7, Nat.add_assoc,
    State.activeWordsAfterUInt256, h16, h17, h512, h544,
    hfirst, hsecond, Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hpush6, word_add_assoc]

/-- Restore the exact five staged copies expected at PC 970. -/
theorem run_stores (template : State) (pc : UInt256) (mem : ByteArray)
    (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX storesProgram
      (WindowTwentyOneGroup.state template pc mem 16 modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.headState template (advancePC 18 pc)
      (WindowCopyMemory.copyMem mem exponent) 18 modulus accumulator exponent counter rest) := by
  have hs := run_tail template pc mem modulus accumulator exponent counter rest hrest
  let core := WindowTwentyOneLookup.framed template (advancePC 13 pc)
    (WindowCopyMemory.copyMem mem exponent) 18 []
  have hh := WindowTwentyOneStage.run_stageHead core (advancePC 13 pc)
    accumulator modulus exponent (UInt256.ofNat 480) counter rest hrest
  have hh' : runInstructions WindowTwentyOneStage.stageHead
      (WindowTwentyOneLookup.framed template (advancePC 13 pc)
        (WindowCopyMemory.copyMem mem exponent) 18
        ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest)) =
      some (WindowTwentyOneLookup.framed template (advancePC 5 (advancePC 13 pc))
        (WindowCopyMemory.copyMem mem exponent) 18
        (List.replicate 5 modulus ++
          ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest))) := by
    simpa only [core, WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed] using hh
  have hx := (runInstructionsX_eq WindowTwentyOneStage.stageHead (by decide) _).trans hh'
  have hall := runInstructionsX_append_some _ _ _ _ _ hs hx
  have hpc : advancePC 5 (advancePC 13 pc) = advancePC 18 pc := rfl
  simpa only [storesProgram, WindowTwentyOneGroup.headState, hpc] using hall

/-- Opcode charges plus the actual two memory expansions, excluding JUMPDEST. -/
def oldTailCharge : Nat :=
  2 * Gas.baseCost .Osaka (.Dup ⟨2, by decide⟩) +
  Gas.baseCost .Osaka (.Push ⟨1, by decide⟩) + Gas.baseCost .Osaka .SHR +
  2 * Gas.baseCost .Osaka (.Push ⟨2, by decide⟩) +
  2 * Gas.baseCost .Osaka .MSTORE +
  MachineState.memExpansionDelta 16 512 32 + MachineState.memExpansionDelta 17 544 32

def newTailCharge : Nat :=
  2 * Gas.baseCost .Osaka (.Dup ⟨2, by decide⟩) +
  Gas.baseCost .Osaka (.Push ⟨5, by decide⟩) + Gas.baseCost .Osaka .SHR +
  2 * Gas.baseCost .Osaka .MSIZE + 2 * Gas.baseCost .Osaka .MSTORE +
  MachineState.memExpansionDelta 16 512 32 + MachineState.memExpansionDelta 17 544 32

theorem charge_difference : oldTailCharge = 30 ∧ newTailCharge = 28 ∧
    oldTailCharge = newTailCharge + 2 := by decide

end Challenge.Modexp.Submission.Proofs.Bytecode.FrontierFirstCopy
