import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLastGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

def entryProgram : List Instr := []

/-- The same two exponent-copy stores, with the immediate narrowed to one byte.
The MSIZE spelling is due to @i34-9. -/
def setupTailProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 1 4, .op .SHR, .op .MSIZE, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .MSIZE, .op .MSTORE]

def trampolineProgram : List Instr := setupTailProgram

def bodyProgram (off : Nat) : List Instr := WindowSixteenBlock.Block.program80 off

def bodyProgramLast (off : Nat) : List Instr := WindowSixteenBody.programLast off

def eAt (exponent : UInt256) (_count : Nat) : UInt256 :=
  UInt256.shiftLeft exponent (UInt256.ofNat 1)

def loopMem (base modulus exponent : UInt256) : Nat → ByteArray
  | 0 => WindowTableMemory.tableMemory base modulus
  | _ + 1 => WindowCopyMemory.copyMem (WindowTableMemory.tableMemory base modulus)
      (eAt exponent 0)

theorem loopMem_table (base modulus exponent : UInt256) (count : Nat) :
    ∀ i, i < 16 → MachineState.readWord (loopMem base modulus exponent count) (32 * i) =
      WindowMath.tableWord base modulus i := by
  intro i hi
  cases count with
  | zero => exact WindowTableMemory.readWord_tableMemory base modulus i hi
  | succ c =>
      rw [loopMem, WindowCopyMemory.readWord_copyMem_low _ _ _ (by omega)]
      exact WindowTableMemory.readWord_tableMemory base modulus i hi

def spare (base modulus exponent : UInt256) : UInt256 :=
  WindowTwentyOneMath.accumulator base modulus exponent.toNat 0

def entryState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template (UInt256.ofNat 988)
    (WindowTableMemory.tableMemory base modulus) 16
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (spare base modulus exponent) 0 rest

/-- Each full block consumes sixteen digits and restores the original frame. -/
def headState (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template pc (loopMem base modulus exponent (count + 1)) 18
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (16 * count))
    (eAt exponent count) (spare base modulus exponent) 0 rest

def postStateLast (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneLastGroup.outState template pc (loopMem base modulus exponent 4) 18
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63)
    (eAt exponent 3) (spare base modulus exponent) rest

def finishState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  postStateLast template (UInt256.ofNat 2377) base modulus exponent rest

private theorem advancePC_ofNat (count pc : Nat) :
    advancePC count (UInt256.ofNat pc) = UInt256.ofNat (pc + count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [advancePC, ih, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_entry (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (_hrest : rest.length ≤ 1000) :
    runInstructions entryProgram (entryState template base modulus exponent rest) =
    some (entryState template base modulus exponent rest) := by
  rfl

theorem run_setupTail (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (hactive : active = 16) (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX setupTailProgram
      (WindowTwentyOneGroup.state template pc mem active modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneLookup.framed template (advancePC 9 pc)
      (WindowCopyMemory.copyMem mem exponent) 18
      ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest)) := by
  subst hactive
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have ha : (UInt256.ofNat 16).toNat = 16 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : MachineState.activeWordsAfter 16 512 32 = 17 := by
    simp [MachineState.activeWordsAfter]
  have h1' : (UInt256.ofNat 17).toNat = 17 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : MachineState.activeWordsAfter 17 544 32 = 18 := by
    simp [MachineState.activeWordsAfter]
  have hpush2 : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructionsX, runInstrX_msize, setupTailProgram, WindowTwentyOneGroup.state,
    WindowTwentyOneLookup.framed,
    WindowCopyMemory.copyMem, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap5, hcap6, hcap7, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hpush2, word_add_assoc]

theorem run_trampoline (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX trampolineProgram (entryState template base modulus exponent rest) =
    some (headState template (UInt256.ofNat 997) base modulus exponent 0 rest) := by
  have hs := run_setupTail template (UInt256.ofNat 988)
    (WindowTableMemory.tableMemory base modulus) 16 rfl modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (spare base modulus exponent) rest hrest
  have hpc : advancePC 9 (UInt256.ofNat 988) = UInt256.ofNat 997 := by decide
  simpa only [trampolineProgram, entryState, headState, loopMem, hpc,
    WindowTwentyOneGroup.state, List.replicate_zero, List.nil_append,
    List.cons_append] using hs

theorem run_body (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count < 3) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (bodyProgram (16 * count))
      (headState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (headState template (UInt256.ofNat (pc + 351)) base modulus exponent (count + 1) rest) := by
  have hb := WindowSixteenBlock.Block.run_program80 template (UInt256.ofNat pc)
    (WindowTableMemory.tableMemory base modulus) base modulus exponent
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (16 * count))
    (spare base modulus exponent) (16 * count) (by omega)
    (loopMem_table base modulus exponent 0) rest hrest
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 16 * count) 16
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat (16 * count)) =
    WindowTwentyOneMath.accumulator base modulus exponent.toNat (16 * (count + 1)) := by
    simpa only [WindowTwentyOneMath.accumulator, Nat.mul_add, Nat.mul_one] using
      (WindowTwentyOneMath.advance_add base modulus exponent.toNat 1 (16 * count) 16
        (WindowTwentyOneMath.initialAccumulator base modulus exponent.toNat)).symm
  rw [ha, advancePC_ofNat] at hb
  simpa only [bodyProgram, headState, loopMem, eAt,
    WindowSixteenBlock.Block.blockMemory] using hb

theorem run_bodyLast (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (bodyProgramLast 48)
      (headState template (UInt256.ofNat pc) base modulus exponent 3 rest) =
    some (postStateLast template (UInt256.ofNat (pc + 327)) base modulus exponent rest) := by
  have hb := WindowSixteenBody.run_last template (UInt256.ofNat pc)
    (WindowTableMemory.tableMemory base modulus) base modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 48) exponent
    (spare base modulus exponent) (loopMem_table base modulus exponent 0) rest hrest
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat 49 15
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 48) =
    WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 :=
    (WindowTwentyOneMath.advance_add base modulus exponent.toNat 1 48 15 _).symm
  rw [ha, advancePC_ofNat] at hb
  simpa only [bodyProgramLast, headState, postStateLast, loopMem, eAt,
    WindowSixteenBlock.Block.blockMemory] using hb

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
