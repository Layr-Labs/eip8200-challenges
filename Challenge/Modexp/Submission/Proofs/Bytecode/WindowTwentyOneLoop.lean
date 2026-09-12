import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTail

set_option warningAsError true

/-!
# The twenty-one-nibble loop with the exponent-copy trampoline (MX)

Each of the three passes enters the trampoline at 5240 (from the loop head `PUSH2 5240
JUMP` at 2495 on the first pass, from the tail's `JUMPI` afterwards).  The trampoline
stores the two exponent copies of the pass's shifted exponent above the table, replays
the first five staging instructions and jumps back to the `JUMPDEST` at 2500, where the
straight-line body resumes.  The memory of pass `count` is `loopMem count`: the table,
overwritten `count` times with fresh copies; only its table words and the last copies
are ever read.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- The loop head at 2495. -/
def entryProgram : List Instr := [.push 2 5240, .op .JUMP]

def setupProgram : List Instr :=
  [.op .JUMPDEST,
   .op (.Dup ⟨2, by decide⟩), .push 1 7, .op .SHR, .push 2 544, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .push 1 3, .op .SHR, .push 2 576, .op .MSTORE]

def backProgram (target : UInt256) : List Instr := [.push 2 target, .op .JUMP]

/-- The trampoline at 5240. -/
def trampolineProgram : List Instr :=
  setupProgram ++ WindowTwentyOneStage.stageHead ++ backProgram (UInt256.ofNat 2500)

/-- The body from the `JUMPDEST` at 2500 through the tail's `JUMPI` at 2957. -/
def bodyProgram : List Instr :=
  [.op .JUMPDEST] ++ WindowTwentyOneBody.program ++ WindowTwentyOneTail.program (UInt256.ofNat 5240)

/-- The exponent word of pass `count`, shifted past the nibbles already consumed. -/
def eAt (exponent : UInt256) (count : Nat) : UInt256 :=
  UInt256.shiftLeft exponent (UInt256.ofNat (4 * (1 + 21 * count)))

def loopMem (base modulus exponent : UInt256) : Nat → ByteArray
  | 0 => WindowTableMemory.tableMemory base modulus
  | count + 1 => WindowCopyMemory.copyMem (loopMem base modulus exponent count) (eAt exponent count)

def loopActive : Nat → Nat
  | 0 => 16
  | _ + 1 => 19

theorem loopMem_table (base modulus exponent : UInt256) (count : Nat) :
    ∀ i, i < 16 → MachineState.readWord (loopMem base modulus exponent count) (32 * i) =
      WindowMath.tableWord base modulus i := by
  induction count with
  | zero =>
      intro i hi
      exact WindowTableMemory.readWord_tableMemory base modulus i hi
  | succ count ih =>
      intro i hi
      rw [loopMem, WindowCopyMemory.readWord_copyMem_low _ _ _ (by omega)]
      exact ih i hi

/-- The loop head, as the table prelude leaves it. -/
def entryState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template (UInt256.ofNat 2495) (WindowTableMemory.tableMemory base modulus) 16
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (UInt256.ofNat 2) 0 rest

/-- Trampoline entry of pass `count`. -/
def loopState (template : State) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template (UInt256.ofNat 5240) (loopMem base modulus exponent count)
    (loopActive count) modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count))
    (eAt exponent count) (UInt256.ofNat (2 - count)) 0 rest

/-- Body entry (2500) of pass `count`, with the pass's copies stored. -/
def headState (template : State) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.headState template (UInt256.ofNat 2500) (loopMem base modulus exponent (count + 1))
    19 modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count))
    (eAt exponent count) (UInt256.ofNat (2 - count)) rest

/-- The final decrement wraps, but no instruction reads this dead counter again. -/
def finishState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template (UInt256.ofNat 2958) (loopMem base modulus exponent 3) 19 modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 63)
    (UInt256.shiftLeft
      (UInt256.shiftLeft exponent (UInt256.ofNat 172)) (UInt256.ofNat 84))
    (UInt256.ofNat 0 - UInt256.ofNat 1) 0 rest

private theorem advancePC_ofNat (count pc : Nat) :
    advancePC count (UInt256.ofNat pc) = UInt256.ofNat (pc + count) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [advancePC, ih, Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_entry (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5240 = true) :
    runInstructions entryProgram (entryState template base modulus exponent rest) =
    some (loopState template base modulus exponent 0 rest) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  simp [runInstructions, entryProgram, entryState, loopState, loopMem, loopActive,
    WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap5, hcap6, Nat.add_assoc, hjump,
    Challenge.EvmProof.Word.literal_eq_ofNat]

/-- `JUMPDEST` and the two copy stores; the first pass also grows memory to 19 words. -/
theorem run_setup (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (hactive : active ≤ 19) (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions setupProgram
      (WindowTwentyOneGroup.state template pc mem active modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneLookup.framed template (advancePC 17 pc)
      (WindowCopyMemory.copyMem mem exponent) 19
      ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest)) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : MachineState.activeWordsAfter active 544 32 = max active 18 := by
    simp [MachineState.activeWordsAfter]
  have h1' : (UInt256.ofNat (max active 18)).toNat = max active 18 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : MachineState.activeWordsAfter (max active 18) 576 32 = 19 := by
    simp [MachineState.activeWordsAfter]
    omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hpush3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, setupProgram, WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    WindowCopyMemory.copyMem, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap5, hcap6, hcap7, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hpush, hpush3, word_add_assoc]

theorem run_back (template : State) (pc target : UInt256) (mem : ByteArray) (active : Nat)
    (stack : List UInt256) (hcap : stack.length + 1 < 1024)
    (htarget : Decode.isValidJumpDest template.executionEnv.code target.toNat = true) :
    runInstructions (backProgram target)
      (WindowTwentyOneLookup.framed template pc mem active stack) =
    some (WindowTwentyOneLookup.framed template target mem active stack) := by
  have hcap0 : stack.length < 1024 := by omega
  simp [runInstructions, backProgram, WindowTwentyOneLookup.framed,
    Challenge.EvmProof.Stepper.runInstr, hcap0, hcap, htarget]

theorem run_trampoline (template : State) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 2500 = true) :
    runInstructions trampolineProgram (loopState template base modulus exponent count rest) =
    some (headState template base modulus exponent count rest) := by
  let mem := loopMem base modulus exponent count
  let a := WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count)
  let e := eAt exponent count
  let c := UInt256.ofNat (2 - count)
  have hactive : loopActive count ≤ 19 := by cases count <;> simp [loopActive]
  have hs := run_setup template (UInt256.ofNat 5240) mem (loopActive count) hactive
    modulus a e c rest hrest
  let core := WindowTwentyOneLookup.framed template (advancePC 17 (UInt256.ofNat 5240))
    (WindowCopyMemory.copyMem mem e) 19 []
  have hh := WindowTwentyOneStage.run_stageHead core (advancePC 17 (UInt256.ofNat 5240))
    a modulus e (UInt256.ofNat 480) c rest hrest
  have hh' : runInstructions WindowTwentyOneStage.stageHead
      (WindowTwentyOneLookup.framed template (advancePC 17 (UInt256.ofNat 5240))
        (WindowCopyMemory.copyMem mem e) 19 ([a, modulus, e, UInt256.ofNat 480, c] ++ rest)) =
      some (WindowTwentyOneLookup.framed template (advancePC 5 (advancePC 17 (UInt256.ofNat 5240)))
        (WindowCopyMemory.copyMem mem e) 19
        (List.replicate 5 modulus ++ ([a, modulus, e, UInt256.ofNat 480, c] ++ rest))) := by
    simpa only [core, WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed] using hh
  have hb := run_back template (advancePC 5 (advancePC 17 (UInt256.ofNat 5240))) (UInt256.ofNat 2500)
    (WindowCopyMemory.copyMem mem e) 19
    (List.replicate 5 modulus ++ ([a, modulus, e, UInt256.ofNat 480, c] ++ rest))
    (by simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]; omega)
    (by rw [show (UInt256.ofNat 2500).toNat = 2500 from rfl]; exact hjump)
  have h1 := runInstructions_append_some _ _ _ _ _ hs hh'
  have hall := runInstructions_append_some _ _ _ _ _ h1 hb
  simpa only [trampolineProgram, loopState, headState, WindowTwentyOneGroup.headState, loopMem,
    mem, a, e, c] using hall

theorem run_body (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count ≤ 2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5240 = true) :
    runInstructions bodyProgram (headState template base modulus exponent count rest) =
    some (WindowTwentyOneGroup.state template
      (if UInt256.isTrue (UInt256.ofNat (2 - count)) then UInt256.ofNat 5240 else UInt256.ofNat 2958)
      (loopMem base modulus exponent (count + 1)) 19 modulus
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
      (UInt256.shiftLeft (eAt exponent count) (UInt256.ofNat 84))
      (UInt256.ofNat (2 - count) - UInt256.ofNat 1) 0 rest) := by
  let mem := loopMem base modulus exponent count
  let a := WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count)
  let e := eAt exponent count
  let c := UInt256.ofNat (2 - count)
  let nextA := WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21)
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 21 * count) 21 a = nextA := by
    dsimp only [a, nextA]
    rw [WindowTwentyOneMath.accumulator_twentyOne]
  have hcap : rest.length + 10 < 1024 := by omega
  have hd : runInstructions [.op .JUMPDEST] (headState template base modulus exponent count rest) =
      some (WindowTwentyOneGroup.headState template (UInt256.ofNat 2501)
        (WindowCopyMemory.copyMem mem e) 19 modulus a e c rest) := by
    simp [runInstructions, headState, WindowTwentyOneGroup.headState, WindowTwentyOneLookup.framed,
      Challenge.EvmProof.Stepper.runInstr, hcap, loopMem, mem, a, e, c,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  have hb := WindowTwentyOneBody.run_twentyOne template (UInt256.ofNat 2501) mem
    base modulus a exponent c (loopMem_table base modulus exponent count)
    (1 + 21 * count) (by omega) rest hrest
  have ht := WindowTwentyOneTail.run_tail template (UInt256.ofNat 2944) (UInt256.ofNat 5240)
    (WindowCopyMemory.copyMem mem e) 19 modulus nextA e c rest hrest
    (by rw [show (UInt256.ofNat 5240).toNat = 5240 from rfl]; exact hjump)
  rw [ha, advancePC_ofNat] at hb
  rw [advancePC_ofNat] at ht
  have hdb := runInstructions_append_some _ _ _ _ _ hd hb
  have hall := runInstructions_append_some _ _ _ _ _ hdb ht
  simpa only [bodyProgram, loopMem, mem, a, e, c, nextA, eAt] using hall

theorem run_continue (template : State) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count < 2)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5240 = true) :
    runInstructions bodyProgram (headState template base modulus exponent count rest) =
    some (loopState template base modulus exponent (count + 1) rest) := by
  have h := run_body template base modulus exponent count (by omega) rest hrest hjump
  have hc : UInt256.isTrue (UInt256.ofNat (2 - count)) := by
    change (2 - count) % (2 ^ 256) ≠ 0
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hsub : UInt256.ofNat (2 - count) - UInt256.ofNat 1 = UInt256.ofNat (2 - (count + 1)) := by
    rw [Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by omega)]
    congr 1
  have hshift : UInt256.shiftLeft (eAt exponent count) (UInt256.ofNat 84) = eAt exponent (count + 1) := by
    unfold eAt
    rw [WindowTwentyOneTail.shift_twentyOne exponent (1 + 21 * count) (by omega)]
    congr 2
  rw [if_pos hc, hsub, hshift, show 21 * count + 21 = 21 * (count + 1) by omega] at h
  simpa only [loopState, loopActive] using h

theorem run_last (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000)
    (hjump : Decode.isValidJumpDest template.executionEnv.code 5240 = true) :
    runInstructions bodyProgram (headState template base modulus exponent 2 rest) =
    some (finishState template base modulus exponent rest) := by
  have h := run_body template base modulus exponent 2 (by decide) rest hrest hjump
  rw [if_neg (by decide : ¬ UInt256.isTrue (UInt256.ofNat (2 - 2)))] at h
  simpa only [finishState, eAt, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub] using h

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
