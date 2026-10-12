import Challenge.Modexp.Submission.Proofs.Bytecode.WindowSixteenBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLastGroup
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneInit

set_option warningAsError true

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

/-- 979..984: the two exponent-copy stores.  The `MSIZE` spelling is due to @i34-9. -/
def trampolineProgram : List Instr :=
  [.op .MSIZE, .op .MSTORE, .op (.Dup ⟨0, by decide⟩), .op .MSIZE, .op .MSTORE]

/-- 984..994: the spare modulus copy and the first-digit lookup. -/
def entryProgram : List Instr := WindowTwentyOneInit.lookupProgram

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

/-- The word under the frame's mask.  Since the setup no longer rotates the
stack, this is the modulus word the route entered with; below it the original
exponent word is still in place, and the ladder reads neither. -/
def spare (_base modulus _exponent : UInt256) : UInt256 := modulus

/-- The state at 979, after `WindowTwentyOneInit.program`. -/
def entryState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneTable.framed template (UInt256.ofNat 979) base modulus 16
    (WindowTwentyOneInit.setupStack modulus exponent rest)

/-- The state at 984, after the two exponent-copy stores. -/
def copiedState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneLookup.framed template (UInt256.ofNat 984) (loopMem base modulus exponent 1) 18
    ([WindowTwentyOneInit.doubled exponent, UInt256.ofNat 480, modulus, exponent] ++ rest)

/-- Each full block consumes sixteen digits and restores the original frame. -/
def headState (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template pc (loopMem base modulus exponent (count + 1)) 18
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (16 * count))
    (eAt exponent count) (spare base modulus exponent) 0 (exponent :: rest)

def postStateLast (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneLastGroup.outState template pc (loopMem base modulus exponent 4) 18
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63)
    (eAt exponent 3) (spare base modulus exponent) (exponent :: rest)

def finishState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  postStateLast template (UInt256.ofNat 2374) base modulus exponent rest

private theorem advancePC_ofNat (count pc : Nat) :
    advancePC count (UInt256.ofNat pc) = UInt256.ofNat (pc + count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [advancePC, ih, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-- The two copies, from the table frame at any `pc`: the active-word count
grows from 16 to 18 and the doubled exponent stays on top. -/
theorem run_copies (template : State) (pc base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 999) :
    runInstructionsX trampolineProgram
      (WindowTwentyOneTable.framed template pc base modulus 16
        (WindowTwentyOneInit.setupStack modulus exponent rest)) =
    some (WindowTwentyOneLookup.framed template (advancePC 5 pc)
      (WindowCopyMemory.copyMem (WindowTableMemory.tableMemory base modulus)
        (WindowTwentyOneInit.doubled exponent)) 18
      ([WindowTwentyOneInit.doubled exponent, UInt256.ofNat 480, modulus, exponent] ++ rest)) := by
  have hcap4 : rest.length + 4 < 1024 := by omega
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have ha : (UInt256.ofNat 16).toNat = 16 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : MachineState.activeWordsAfter 16 512 32 = 17 := by
    simp [MachineState.activeWordsAfter]
  have h1' : (UInt256.ofNat 17).toNat = 17 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : MachineState.activeWordsAfter 17 544 32 = 18 := by
    simp [MachineState.activeWordsAfter]
  simp [runInstructionsX, runInstrX_msize, trampolineProgram,
    WindowTwentyOneInit.setupStack, WindowTwentyOneInit.quartered,
    WindowTwentyOneTable.framed, WindowTwentyOneLookup.framed,
    WindowTableMemory.tableMemory,
    WindowCopyMemory.copyMem, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap4, hcap5, hcap6, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    advancePC, succ_eq_add, word_add_assoc]

theorem run_trampoline (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 999) :
    runInstructionsX trampolineProgram (entryState template base modulus exponent rest) =
    some (copiedState template base modulus exponent rest) := by
  have hs := run_copies template (UInt256.ofNat 979) base modulus exponent rest hrest
  have hpc : advancePC 5 (UInt256.ofNat 979) = UInt256.ofNat 984 := by decide
  rw [hpc] at hs
  simpa only [entryState, copiedState, loopMem, eAt, WindowTwentyOneInit.doubled] using hs

theorem run_entry (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 999) :
    runInstructions entryProgram (copiedState template base modulus exponent rest) =
    some (headState template (UInt256.ofNat 994) base modulus exponent 0 rest) := by
  have h := WindowTwentyOneInit.run_lookup template (UInt256.ofNat 984)
    (loopMem base modulus exponent 1) base modulus exponent
    (loopMem_table base modulus exponent 1) rest (by omega)
  have hpc : advancePC 10 (UInt256.ofNat 984) = UInt256.ofNat 994 := by decide
  rw [hpc] at h
  simpa only [entryProgram, copiedState, headState, spare, eAt, WindowTwentyOneInit.doubled,
    WindowTwentyOneMath.accumulator, WindowTwentyOneMath.advance, Nat.mul_zero] using h

theorem run_body (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count < 3) (rest : List UInt256) (hrest : rest.length ≤ 999) :
    runInstructions (bodyProgram (16 * count))
      (headState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (headState template (UInt256.ofNat (pc + 351)) base modulus exponent (count + 1) rest) := by
  have hrest' : (exponent :: rest).length ≤ 1000 := by
    simp only [List.length_cons]; omega
  have hb := WindowSixteenBlock.Block.run_program80 template (UInt256.ofNat pc)
    (WindowTableMemory.tableMemory base modulus) base modulus exponent
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (16 * count))
    (spare base modulus exponent) (16 * count) (by omega)
    (loopMem_table base modulus exponent 0) (exponent :: rest) hrest'
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
    (rest : List UInt256) (hrest : rest.length ≤ 999) :
    runInstructions (bodyProgramLast 48)
      (headState template (UInt256.ofNat pc) base modulus exponent 3 rest) =
    some (postStateLast template (UInt256.ofNat (pc + 327)) base modulus exponent rest) := by
  have hrest' : (exponent :: rest).length ≤ 1000 := by
    simp only [List.length_cons]; omega
  have hb := WindowSixteenBody.run_last template (UInt256.ofNat pc)
    (WindowTableMemory.tableMemory base modulus) base modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 48) exponent
    (spare base modulus exponent) (loopMem_table base modulus exponent 0) (exponent :: rest) hrest'
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat 49 15
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 48) =
    WindowTwentyOneMath.accumulator base modulus exponent.toNat 63 :=
    (WindowTwentyOneMath.advance_add base modulus exponent.toNat 1 48 15 _).symm
  rw [ha, advancePC_ofNat] at hb
  simpa only [bodyProgramLast, headState, postStateLast, loopMem, eAt,
    WindowSixteenBlock.Block.blockMemory] using hb

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
