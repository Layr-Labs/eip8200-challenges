import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTail
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneMsize

set_option warningAsError true

/-!
# The twenty-one-nibble window loop, fully unrolled (MX)

The window core raises the base to the exponent in three passes of twenty-one
nibbles each.  In **this** image the loop is unrolled: there is no `JUMP` and no
`JUMPI` anywhere between pc 900 and pc 1600, and the three passes are three
distinct straight-line regions rather than one block reached three times.

| pass | stores + staging head | body (21 nibbles) | link |
|------|-----------------------|-------------------|------|
| 0    | 952..969 (`storesProgram`)              | 970..1412  | 1413..1417 |
| 1    | carried by pass 0's link                | 1418..1860 | 1861..1865 |
| 2    | carried by pass 1's link                | 1866..2308 | falls into the return at 2309 |

There is no `JUMPDEST` in the region any more: the fall-through head the unroller
left at 951 is gone, together with the old loop tail -- the counter decrement
`PUSH1 1; DUP6; SUB; SWAP5` and the `PUSH2 951; JUMPI`.  All that survives of it is
the four-instruction exponent shift `SWAP2; PUSH1 84; SHL; SWAP2`, which opens each
`linkProgram`.

Consequently there is no pass counter.  The slot beneath the frame that used to hold
the constant `2` now holds a second copy of the initial accumulator, left by the
`DUP4; DUP4` that closes `WindowTwentyOneInit`; every state below carries that same
word and no instruction reads it again.  The memory of pass `count` is `loopMem count`: the table, overwritten
`count` times with fresh exponent copies; only its table words and the last
copies are ever read.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel WindowTwentyOneMsize

/-- The loop head at 952.  Nothing jumps to it; it costs no instruction. -/
def entryProgram : List Instr := []

/-- The two exponent-copy stores: eight instructions, thirteen bytes.  The two store
addresses are read off `MSIZE` rather than pushed: here the table prelude has left exactly
sixteen active words, so the first `MSIZE` is 512 and, after that store, the second is 544 --
the literals the older spelling pushed.  `MSIZE` costs 2 gas against a `PUSH`'s 3, and the two
freed bytes widen the `PUSH1 4` to `PUSH5 4` (same value, same cost), so the program keeps its
thirteen bytes.  Because `MSIZE` reads the active-word count, the lemma below holds only at
`active = 16`, its one use. (This spelling of the stores is due to @i34-9.) -/
def setupTailProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 5 4, .op .SHR, .op .MSIZE, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .op .MSIZE, .op .MSTORE]

/-- The stores followed by the five staging instructions the body expects:
thirteen instructions, eighteen bytes.  Shared by the trampoline and the link. -/
def storesProgram : List Instr := setupTailProgram ++ WindowTwentyOneStage.stageHead

/-- The first pass's trampoline at 952: the stores and the staging head, with no
`JUMPDEST` in front of them. -/
def trampolineProgram : List Instr := storesProgram

/-- The first inter-pass link carries no filler any more: the eighteen dead bytes that used to
sit at pc 1413 (a discarded `PUSH16; POP`) are moved behind the final `RETURN`, where they are
never executed, and the second pass's body starts five bytes after the first pass's body ends. -/
def padProgramA : List Instr := []

/-- The second inter-pass link, likewise without filler. -/
def padProgramB : List Instr := []

/-- Between two passes: replay the staging head.  Five bytes. -/
def linkProgram : List Instr := padProgramA ++ WindowTwentyOneStage.stageHead

def linkProgramB : List Instr := padProgramB ++ WindowTwentyOneStage.stageHead

/-- One pass's body: twenty-one nibbles at address offset `off`.  Four hundred and
forty-three bytes, at 970, 1418 and 1866. -/
def bodyProgram (off : Nat) : List Instr := WindowTwentyOneBody.program off

/-- The last pass's body: its final digit is nibble 0, read off the frame. -/
def bodyProgramLast (off : Nat) : List Instr := WindowTwentyOneBody.programLastPass off

/-- The stored exponent, which no longer depends on the pass: ONE store at 952 serves
every addressed digit. -/
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

/-- The word the init leaves in the former counter slot: a copy of the initial
accumulator. -/
def spare (base modulus exponent : UInt256) : UInt256 :=
  WindowTwentyOneMath.accumulator base modulus exponent.toNat 0

/-- The loop head at 952, as the init leaves it: sixteen active words (the table
only) and the spare accumulator copy beneath the frame. -/
def entryState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template (UInt256.ofNat 952)
    (WindowTableMemory.tableMemory base modulus) 16
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (spare base modulus exponent) 0 rest

/-- Body entry of pass `count` -- 970, 1418, 1866 -- with the pass's copies
stored and the five modulus copies staged. -/
def headState (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.headState template pc (loopMem base modulus exponent (count + 1)) 18
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count))
    (eAt exponent count) (spare base modulus exponent) rest

/-- After pass `count`'s twenty-one nibbles -- 1413, 1861, 2309.  The accumulator
has advanced by twenty-one nibbles; the exponent has not yet been shifted. -/
def postState (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template pc (loopMem base modulus exponent (count + 1)) 18
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
    (eAt exponent count) (spare base modulus exponent) 0 rest

/-- The return entry at 2309, where the third pass falls through.  The spare slot
still holds the copy the init left: nothing ever touched it. -/
def finishState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  postState template (UInt256.ofNat 2309) base modulus exponent 2 rest

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
    some (WindowTwentyOneLookup.framed template (advancePC 13 pc)
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
  have hpush6 : UInt256.ofNat 6 =
      UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 +
      UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructionsX, runInstrX_msize, setupTailProgram, WindowTwentyOneGroup.state,
    WindowTwentyOneLookup.framed,
    WindowCopyMemory.copyMem, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap5, hcap6, hcap7, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hpush6, word_add_assoc]

/-- The stores and the staging head, shared by the trampoline at 952 and the two
links at 1413 and 1861.  Eighteen bytes. -/
theorem run_stores (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (hactive : active = 16) (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX storesProgram
      (WindowTwentyOneGroup.state template pc mem active modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.headState template (advancePC 18 pc)
      (WindowCopyMemory.copyMem mem exponent) 18 modulus accumulator exponent counter rest) := by
  have hs := run_setupTail template pc mem active hactive modulus accumulator exponent counter rest hrest
  let core := WindowTwentyOneLookup.framed template (advancePC 13 pc)
    (WindowCopyMemory.copyMem mem exponent) 18 []
  have hh := WindowTwentyOneStage.run_stageHead core (advancePC 13 pc)
    accumulator modulus exponent (UInt256.ofNat 480) counter rest hrest
  have hh' : runInstructionsX WindowTwentyOneStage.stageHead
      (WindowTwentyOneLookup.framed template (advancePC 13 pc)
        (WindowCopyMemory.copyMem mem exponent) 18
        ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest)) =
      some (WindowTwentyOneLookup.framed template (advancePC 5 (advancePC 13 pc))
        (WindowCopyMemory.copyMem mem exponent) 18
        (List.replicate 5 modulus ++
          ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest))) := by
    rw [runInstructionsX_eq WindowTwentyOneStage.stageHead (by rfl)]
    simpa only [core, WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed] using hh
  have hall := runInstructionsX_append_some _ _ _ _ _ hs hh'
  have hpc : advancePC 5 (advancePC 13 pc) = advancePC 18 pc := rfl
  simpa only [storesProgram, WindowTwentyOneGroup.headState, hpc] using hall

/-- The first pass's trampoline: the stores at 952, landing on the body at 970. -/
theorem run_trampoline (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructionsX trampolineProgram (entryState template base modulus exponent rest) =
    some (headState template (UInt256.ofNat 970) base modulus exponent 0 rest) := by
  have hs := run_stores template (UInt256.ofNat 952)
    (WindowTableMemory.tableMemory base modulus) 16 rfl modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (spare base modulus exponent) rest hrest
  have hpc : advancePC 18 (UInt256.ofNat 952) = UInt256.ofNat 970 := by decide
  simpa only [trampolineProgram, entryState, headState, loopMem, hpc] using hs

/-- One pass's twenty-one nibbles at body pc 970 or 1418.  Four hundred and forty-three
bytes; the exponent and the dead counter are preserved. -/
theorem run_body (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count < 2) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (bodyProgram (21 * count))
      (headState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (postState template (UInt256.ofNat (pc + 443)) base modulus exponent count rest) := by
  have hb := WindowTwentyOneBody.run_twentyOne template (UInt256.ofNat pc)
    (WindowTableMemory.tableMemory base modulus) base modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count)) exponent
    (spare base modulus exponent) (loopMem_table base modulus exponent 0)
    (21 * count) (by omega) rest hrest
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 21 * count) 21
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count)) =
      WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21) :=
    (WindowTwentyOneMath.accumulator_twentyOne base modulus exponent.toNat (21 * count)).symm
  rw [ha, advancePC_ofNat] at hb
  simpa only [bodyProgram, headState, postState, loopMem, eAt] using hb

/-- The final pass at 1866: digits 42..62, the last of them nibble 0. -/
theorem run_bodyLast (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (bodyProgramLast 42)
      (headState template (UInt256.ofNat pc) base modulus exponent 2 rest) =
    some (postState template (UInt256.ofNat (pc + 443)) base modulus exponent 2 rest) := by
  have hb := WindowTwentyOneBody.run_twentyOneLast template (UInt256.ofNat pc)
    (WindowTableMemory.tableMemory base modulus) base modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 42) exponent
    (spare base modulus exponent) (loopMem_table base modulus exponent 0)
    42 rfl rest hrest
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 42) 21
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat 42) =
      WindowTwentyOneMath.accumulator base modulus exponent.toNat (42 + 21) :=
    (WindowTwentyOneMath.accumulator_twentyOne base modulus exponent.toNat 42).symm
  rw [ha, advancePC_ofNat] at hb
  simpa only [bodyProgramLast, headState, postState, loopMem, eAt] using hb

private theorem run_padA (template : State) (pc : UInt256) (mem : ByteArray)
    (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (_hrest : rest.length ≤ 1000) :
    runInstructions padProgramA
      (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 0 pc) mem 18 modulus accumulator
      exponent counter 0 rest) := rfl

private theorem run_padB (template : State) (pc : UInt256) (mem : ByteArray)
    (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (_hrest : rest.length ≤ 1000) :
    runInstructions padProgramB
      (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.state template (advancePC 0 pc) mem 18 modulus accumulator
      exponent counter 0 rest) := rfl

private theorem run_linkOf (pad : List Instr) (w : Nat)
    (hpad : ∀ (template : State) (pc : UInt256) (mem : ByteArray)
      (modulus accumulator exponent counter : UInt256) (rest : List UInt256),
      rest.length ≤ 1000 →
      runInstructions pad
        (WindowTwentyOneGroup.state template pc mem 18 modulus accumulator exponent counter 0 rest) =
      some (WindowTwentyOneGroup.state template (advancePC w pc) mem 18 modulus accumulator
        exponent counter 0 rest))
    (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions (pad ++ WindowTwentyOneStage.stageHead)
      (postState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (headState template (UInt256.ofNat (pc + (w + 5))) base modulus exponent (count + 1) rest) := by
  have hp := hpad template (UInt256.ofNat pc) (loopMem base modulus exponent (count + 1))
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
    (eAt exponent count) (spare base modulus exponent) rest hrest
  let core := WindowTwentyOneLookup.framed template (advancePC w (UInt256.ofNat pc))
    (loopMem base modulus exponent (count + 1)) 18 []
  have hh := WindowTwentyOneStage.run_stageHead core (advancePC w (UInt256.ofNat pc))
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21)) modulus
    (eAt exponent count) (UInt256.ofNat 480) (spare base modulus exponent) rest hrest
  have hh' : runInstructions WindowTwentyOneStage.stageHead
      (WindowTwentyOneGroup.state template (advancePC w (UInt256.ofNat pc))
        (loopMem base modulus exponent (count + 1)) 18 modulus
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
        (eAt exponent count) (spare base modulus exponent) 0 rest) =
      some (WindowTwentyOneGroup.headState template (advancePC 5 (advancePC w (UInt256.ofNat pc)))
        (loopMem base modulus exponent (count + 1)) 18 modulus
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
        (eAt exponent count) (spare base modulus exponent) rest) := by
    simpa only [WindowTwentyOneGroup.state, WindowTwentyOneGroup.headState, core,
      WindowTwentyOneStage.framed, WindowTwentyOneLookup.framed,
      List.replicate_zero, List.nil_append, List.cons_append, List.append_assoc] using hh
  have hall := runInstructions_append_some _ _ _ _ _ (by simpa only [postState] using hp) hh'
  rw [advancePC_ofNat, advancePC_ofNat] at hall
  have hpc : pc + w + 5 = pc + (w + 5) := by omega
  rw [hpc] at hall
  simpa only [postState, headState, loopMem, eAt, Nat.mul_add, Nat.mul_one] using hall

/-- Between passes 0 and 1 (pc 1413): the staging head. -/
theorem run_link (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (_hcount : count < 2) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions linkProgram
      (postState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (headState template (UInt256.ofNat (pc + 5)) base modulus exponent (count + 1) rest) :=
  run_linkOf padProgramA 0
    (fun template pc mem modulus accumulator exponent counter rest hrest =>
      run_padA template pc mem modulus accumulator exponent counter rest hrest)
    template pc base modulus exponent count rest hrest

/-- Between passes 1 and 2 (pc 1879): the same eighteen bytes in eleven instructions. -/
theorem run_linkB (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (_hcount : count < 2) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions linkProgramB
      (postState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (headState template (UInt256.ofNat (pc + 5)) base modulus exponent (count + 1) rest) :=
  run_linkOf padProgramB 0
    (fun template pc mem modulus accumulator exponent counter rest hrest =>
      run_padB template pc mem modulus accumulator exponent counter rest hrest)
    template pc base modulus exponent count rest hrest

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
