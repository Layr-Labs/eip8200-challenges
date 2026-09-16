import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneBody
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneTail

set_option warningAsError true

/-!
# The twenty-one-nibble window loop, fully unrolled (MX)

The window core raises the base to the exponent in three passes of twenty-one
nibbles each.  In **this** image the loop is unrolled: there is no `JUMP` and no
`JUMPI` anywhere between pc 900 and pc 1600, and the three passes are three
distinct straight-line regions rather than one block reached three times.

| pass | stores + staging head | body (21 nibbles) | link |
|------|-----------------------|-------------------|------|
| 0    | 951..969 (`JUMPDEST` + `storesProgram`) | 970..1412  | 1413..1435 |
| 1    | carried by pass 0's link                | 1436..1878 | 1879..1901 |
| 2    | carried by pass 1's link                | 1902..2344 | falls into the return at 2345 |

`JUMPDEST` at 951 is the only one in the region and nothing pushes it; it is the
fall-through head left by the unroller.  Because control never returns to it, the
old loop tail -- the counter decrement `PUSH1 1; DUP6; SUB; SWAP5` and the
`PUSH2 951; JUMPI` -- is gone.  All that survives of it is the four-instruction
exponent shift `SWAP2; PUSH1 84; SHL; SWAP2`, which opens each `linkProgram`.

Consequently the pass counter is never decremented.  `WindowTwentyOneInit` pushes
`2` and every state below carries that same constant; no instruction reads it
again.  The memory of pass `count` is `loopMem count`: the table, overwritten
`count` times with fresh exponent copies; only its table words and the last
copies are ever read.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open WindowNibbleKernel

/-- The loop head at 951.  Nothing jumps to it; it costs no instruction. -/
def entryProgram : List Instr := []

/-- The two exponent-copy stores, without the leading `JUMPDEST`: eight
instructions, thirteen bytes. -/
def setupTailProgram : List Instr :=
  [.op (.Dup ⟨2, by decide⟩), .push 1 4, .op .SHR, .push 2 512, .op .MSTORE,
   .op (.Dup ⟨2, by decide⟩), .push 2 544, .op .MSTORE]

/-- The stores followed by the five staging instructions the body expects:
thirteen instructions, eighteen bytes.  Shared by the trampoline and the link. -/
def storesProgram : List Instr := setupTailProgram ++ WindowTwentyOneStage.stageHead

/-- The first pass's trampoline at 951; only this copy carries the `JUMPDEST`. -/
def trampolineProgram : List Instr := .op .JUMPDEST :: storesProgram

/-- The exponent shift that ends a continuing pass: four instructions, five
bytes.  This is what remains of the old loop tail. -/
def shiftProgram : List Instr :=
  [.op (.Swap ⟨1, by decide⟩), .push 1 84, .op .SHL, .op (.Swap ⟨1, by decide⟩)]

/-- Between two passes (pc 1413 and pc 1879): shift the exponent, store the next
pass's copies, replay the staging head.  Seventeen instructions, twenty-three
bytes. -/
def linkProgram : List Instr := shiftProgram ++ storesProgram

/-- One pass's body: the twenty-one nibbles and nothing else.  Four hundred and
one instructions, four hundred and forty-three bytes, at 970, 1436 and 1902. -/
def bodyProgram : List Instr := WindowTwentyOneBody.program

def eAt (exponent : UInt256) (count : Nat) : UInt256 :=
  UInt256.shiftLeft exponent (UInt256.ofNat (4 * (1 + 21 * count) - 3))

def loopMem (base modulus exponent : UInt256) : Nat → ByteArray
  | 0 => WindowTableMemory.tableMemory base modulus
  | count + 1 => WindowCopyMemory.copyMem (loopMem base modulus exponent count) (eAt exponent count)

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

/-- The loop head at 951, as the table prelude leaves it: sixteen active words
(the table only) and the counter `2` the init pushed. -/
def entryState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template (UInt256.ofNat 951)
    (WindowTableMemory.tableMemory base modulus) 16
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (UInt256.ofNat 2) 0 rest

/-- Body entry of pass `count` -- 970, 1436, 1902 -- with the pass's copies
stored and the five modulus copies staged. -/
def headState (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.headState template pc (loopMem base modulus exponent (count + 1)) 18
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count))
    (eAt exponent count) (UInt256.ofNat 2) rest

/-- After pass `count`'s twenty-one nibbles -- 1413, 1879, 2345.  The accumulator
has advanced by twenty-one nibbles; the exponent has not yet been shifted. -/
def postState (template : State) (pc : UInt256) (base modulus exponent : UInt256)
    (count : Nat) (rest : List UInt256) : State :=
  WindowTwentyOneGroup.state template pc (loopMem base modulus exponent (count + 1)) 18
    modulus (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
    (eAt exponent count) (UInt256.ofNat 2) 0 rest

/-- The return entry at 2345, where the third pass falls through.  The counter is
still the `2` the init pushed: nothing ever decremented it. -/
def finishState (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) : State :=
  postState template (UInt256.ofNat 2345) base modulus exponent 2 rest

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
    (hactive : active ≤ 18) (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions setupTailProgram
      (WindowTwentyOneGroup.state template pc mem active modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneLookup.framed template (advancePC 13 pc)
      (WindowCopyMemory.copyMem mem exponent) 18
      ([accumulator, modulus, exponent, UInt256.ofNat 480, counter] ++ rest)) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hcap7 : rest.length + 7 < 1024 := by omega
  have ha : (UInt256.ofNat active).toNat = active := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h1 : MachineState.activeWordsAfter active 512 32 = max active 17 := by
    simp [MachineState.activeWordsAfter]
  have h1' : (UInt256.ofNat (max active 17)).toNat = max active 17 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : MachineState.activeWordsAfter (max active 17) 544 32 = 18 := by
    simp [MachineState.activeWordsAfter]
    omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hpush3 : UInt256.ofNat 3 = UInt256.ofNat 1 + UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  simp [runInstructions, setupTailProgram, WindowTwentyOneGroup.state, WindowTwentyOneLookup.framed,
    WindowCopyMemory.copyMem, WindowTableMemory.storeWord,
    Challenge.EvmProof.Stepper.runInstr, hcap5, hcap6, hcap7, Nat.add_assoc,
    State.activeWordsAfterUInt256, ha, h1, h1', h2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    advancePC, succ_eq_add, hpush, hpush3, word_add_assoc]

/-- The stores and the staging head, shared by the trampoline at 951 and the two
links at 1413 and 1879.  Eighteen bytes. -/
theorem run_stores (template : State) (pc : UInt256) (mem : ByteArray) (active : Nat)
    (hactive : active ≤ 18) (modulus accumulator exponent counter : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions storesProgram
      (WindowTwentyOneGroup.state template pc mem active modulus accumulator exponent counter 0 rest) =
    some (WindowTwentyOneGroup.headState template (advancePC 18 pc)
      (WindowCopyMemory.copyMem mem exponent) 18 modulus accumulator exponent counter rest) := by
  have hs := run_setupTail template pc mem active hactive modulus accumulator exponent counter rest hrest
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
  have hall := runInstructions_append_some _ _ _ _ _ hs hh'
  have hpc : advancePC 5 (advancePC 13 pc) = advancePC 18 pc := rfl
  simpa only [storesProgram, WindowTwentyOneGroup.headState, hpc] using hall

/-- The first pass's trampoline: the fall-through `JUMPDEST` at 951 and the
stores, landing on the body at 970. -/
theorem run_trampoline (template : State) (base modulus exponent : UInt256)
    (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions trampolineProgram (entryState template base modulus exponent rest) =
    some (headState template (UInt256.ofNat 970) base modulus exponent 0 rest) := by
  have hhead := WindowTwentyOneTail.run_head template (UInt256.ofNat 951)
    (WindowTableMemory.tableMemory base modulus) 16 modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (UInt256.ofNat 2) rest hrest
  have hs := run_stores template (UInt256.ofNat 951).succ
    (WindowTableMemory.tableMemory base modulus) 16 (by omega) modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat 0)
    (eAt exponent 0) (UInt256.ofNat 2) rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hhead hs
  have hpc : advancePC 18 (UInt256.ofNat 951).succ = UInt256.ofNat 970 := by decide
  simpa only [trampolineProgram, entryState, headState, loopMem, hpc,
    List.cons_append, List.nil_append] using hall

/-- One pass's twenty-one nibbles, at any of the three body pcs.  Four hundred
and forty-three bytes; the exponent and the dead counter are preserved. -/
theorem run_body (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count ≤ 2) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions bodyProgram
      (headState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (postState template (UInt256.ofNat (pc + 443)) base modulus exponent count rest) := by
  have hb := WindowTwentyOneBody.run_twentyOne template (UInt256.ofNat pc)
    (loopMem base modulus exponent count) base modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count)) exponent
    (UInt256.ofNat 2) (loopMem_table base modulus exponent count)
    (1 + 21 * count) (by omega) (by omega) rest hrest
  have ha : WindowTwentyOneMath.advance base modulus exponent.toNat (1 + 21 * count) 21
      (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count)) =
      WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21) := by
    rw [WindowTwentyOneMath.accumulator_twentyOne]
  rw [ha, advancePC_ofNat] at hb
  simpa only [bodyProgram, headState, postState, loopMem, eAt] using hb

/-- The link between two passes: shift the exponent by one window, store the next
pass's copies, replay the staging head.  Twenty-three bytes. -/
theorem run_link (template : State) (pc : Nat) (base modulus exponent : UInt256)
    (count : Nat) (hcount : count < 2) (rest : List UInt256) (hrest : rest.length ≤ 1000) :
    runInstructions linkProgram
      (postState template (UInt256.ofNat pc) base modulus exponent count rest) =
    some (headState template (UInt256.ofNat (pc + 23)) base modulus exponent (count + 1) rest) := by
  have hcap5 : rest.length + 5 < 1024 := by omega
  have hcap6 : rest.length + 6 < 1024 := by omega
  have hpush : UInt256.ofNat 2 = UInt256.ofNat 1 + UInt256.ofNat 1 := by decide
  have hshift : UInt256.shiftLeft (eAt exponent count) (UInt256.ofNat 84) = eAt exponent (count + 1) := by
    unfold eAt
    rw [WindowTwentyOneTail.shift_twentyOne exponent (1 + 21 * count) (by omega) (by omega)]
    congr 2
  have hsh : runInstructions shiftProgram
      (postState template (UInt256.ofNat pc) base modulus exponent count rest) =
      some (WindowTwentyOneGroup.state template (advancePC 5 (UInt256.ofNat pc))
        (loopMem base modulus exponent (count + 1)) 18 modulus
        (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
        (eAt exponent (count + 1)) (UInt256.ofNat 2) 0 rest) := by
    rw [← hshift]
    simp [runInstructions, shiftProgram, postState, WindowTwentyOneGroup.state,
      WindowTwentyOneLookup.framed, Challenge.EvmProof.Stepper.runInstr,
      hcap5, hcap6, Nat.add_assoc, List.exchange,
      advancePC, succ_eq_add, hpush, word_add_assoc,
      Challenge.EvmProof.Word.literal_eq_ofNat]
  have hs := run_stores template (advancePC 5 (UInt256.ofNat pc))
    (loopMem base modulus exponent (count + 1)) 18 (by omega) modulus
    (WindowTwentyOneMath.accumulator base modulus exponent.toNat (21 * count + 21))
    (eAt exponent (count + 1)) (UInt256.ofNat 2) rest hrest
  have hall := runInstructions_append_some _ _ _ _ _ hsh hs
  rw [advancePC_ofNat] at hall
  rw [advancePC_ofNat] at hall
  have hacc : 21 * count + 21 = 21 * (count + 1) := by omega
  have hpc : pc + 5 + 18 = pc + 23 := by omega
  simpa only [linkProgram, headState, loopMem, hacc, hpc] using hall

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneLoop
