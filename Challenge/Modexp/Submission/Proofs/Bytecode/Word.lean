import Challenge.Modexp.Submission.Proofs.Algorithm
import Challenge.Modexp.Submission.Proofs.Bytecode.Accessors
import Challenge.Modexp.Submission.Proofs.Bytecode.Dispatch
import Challenge.Modexp.Submission.Proofs.Bytecode.WordPC
import Challenge.EvmProof.Bytes
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option maxErrors 1
/-!
# One-word MODEXP path: 4-bit windows over a word-at-a-time base

The `modexpWord` region at byte `0x021a` is a three-instruction trampoline into
an appended body at byte `0x07e3` (instruction indices 1495–1737).  The body

* reduces the base a full 32-byte word at a time in radix `2^256`, using
  `R := addmod(mod(not 0, m), 1, m)`;
* tabulates `T[k] = base^k mod m` for `k < 16` in memory `[0x0000, 0x0200)`;
* consumes the exponent one byte at a time as two 4-bit windows, four squarings
  and one table multiply each.

Three facts the proof carries deliberately.

1. `SHR` by 256 or more is `0`.  That is what makes `bsize mod 32 = 0` correct:
   `shr(256, calldataload(96))` is the empty leading partial word.
   `EvmProof.Bytes.shiftRight_readWord` carries `0 < width` and does not cover
   it, so `lead_shift` splits the case and closes it with `shiftRight_full`.
2. The window mask `0x1E0` keeps every `MLOAD` inside the table for *any* `w`,
   but selects the intended entry only when `w < 256`.  That bound is a
   hypothesis of `maskHi`/`maskLo`, never an inference from the mask; it holds
   because `w` is produced by `BYTE(0, ·)`.
3. `T[0]` is `mod(1, m)`, never the literal `1`.  When `Esize = 0` the byte
   loop never runs and `T[0]` is returned with no trailing `MULMOD`, so `m = 1`
   must give `0`.

**Region ownership (constraint C1 of `merged_layout.json`).**  The window table
occupies `[0x0000, 0x0200)`, which the big path's `addMaskedMod` also reads as
its modulus buffer.  The two are safe only because the paths are mutually
exclusive: this module's entry (`run_startLoad`) reads the modulus from
*calldata*, and the only exits are `RETURN`s — `run_zeroTail` for the
zero-modulus case and, for the normal case, `run_byteJumpi_exit` into
`run_byteExit`/`run_byteExitJump`, which hand control to the unchanged block at
`0x029d`.  None of those lemmas re-enters the dispatcher.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Word

open EvmSemantics
open EvmSemantics.EVM

attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

/-! ## Operand offsets and the calling frame -/

def expOffset (input : ByteArray) : Nat := 96 + baseSize input
def modulusOffset (input : ByteArray) : Nat := expOffset input + exponentSize input

def modulusValue (input : ByteArray) : Nat :=
  Precompile.bytesToNatPadded input (modulusOffset input) (modulusSize input)

def callerRest (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusOffset input), UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusSize input), UInt256.ofNat (exponentSize input),
    UInt256.ofNat (baseSize input)]

/-- The 13-word frame the word path carries unchanged from `0x021a` to
`0x029d`.  Every state below is this frame with a few scratch words on top. -/
def wordFrame (input : ByteArray) : List UInt256 :=
  [UInt256.ofNat (modulusValue input), UInt256.ofNat (baseSize input),
    UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
    UInt256.ofNat 96, UInt256.ofNat (expOffset input),
    UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input

def nonzeroState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 538
    stack := wordFrame input }

def loadedState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 532
    stack := (538 : UInt256) :: UInt256.ofNat (modulusValue input) ::
      (nonzeroState input).stack }

def zeroDispatchState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 533 }

def zeroModulusFinalState (input : ByteArray) : State :=
  { Dispatch.wordEntryState input with
    pc := UInt256.ofNat 537
    stack := [UInt256.ofNat 0, UInt256.ofNat (baseSize input),
      UInt256.ofNat (exponentSize input), UInt256.ofNat (modulusSize input),
      UInt256.ofNat 96, UInt256.ofNat (expOffset input),
      UInt256.ofNat (modulusOffset input), UInt256.ofNat 1267] ++ callerRest input
    halt := .Returned
    hReturn := MachineState.readPadded ByteArray.empty 6144 (modulusSize input)
    activeWords := (Dispatch.wordEntryState input).activeWordsAfterUInt256
      6144 (modulusSize input) }

def byteWord (input : ByteArray) (offset : Nat) : UInt256 :=
  Accessors.calldataByteValue (Dispatch.wordEntryState input) (UInt256.ofNat offset)

/-! ## States of the appended body

Instruction indices 1495–1737, byte `0x07e3`–`0x0905`.  The in-place region at
`0x021a` is a three-instruction trampoline. -/

/-- Entry of the appended body, reached by the trampoline `JUMP`. -/
def wordBodyState (input : ByteArray) : State :=
  { nonzeroState input with pc := UInt256.ofNat 2019 }

/-- `R := addmod(mod(not 0, m), 1, m)`, the radix `2^256 mod m`. -/
def radixWord (input : ByteArray) : UInt256 :=
  UInt256.addMod (UInt256.lnot 0 % UInt256.ofNat (modulusValue input)) 1
    (UInt256.ofNat (modulusValue input))

/-! ### Word-at-a-time base reduction -/

/-- Width of the leading partial word of the base, `bsize mod 32`. -/
def leadWidth (input : ByteArray) : Nat := baseSize input % 32

/-- Calldata pointer after `k` full base words have been consumed. -/
def basePtr (input : ByteArray) (k : Nat) : Nat := 96 + leadWidth input + 32 * k

/-- The leading partial word, reduced.  `shr(256, ·)` is `0`, which is what
makes the `bsize mod 32 = 0` case correct. -/
def baseInit (input : ByteArray) : UInt256 :=
  UInt256.ofNat
    (Precompile.bytesToNatPadded input 96 (leadWidth input) % modulusValue input)

def hornerStep (input : ByteArray) (k : Nat) (base : UInt256) : UInt256 :=
  UInt256.addMod
    (UInt256.mulMod base (radixWord input) (UInt256.ofNat (modulusValue input)))
    (MachineState.readWord input (basePtr input k))
    (UInt256.ofNat (modulusValue input))

def hornerAfter (input : ByteArray) : Nat → UInt256
  | 0 => baseInit input
  | k + 1 => hornerStep input k (hornerAfter input k)

def baseLoopState (input : ByteArray) (k : Nat) (base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 2051
    stack := [UInt256.ofNat (basePtr input k), base, radixWord input] ++
      wordFrame input }

def baseBodyState (input : ByteArray) (k : Nat) (base : UInt256) : State :=
  { baseLoopState input k base with pc := UInt256.ofNat 2060 }

def baseExitState (input : ByteArray) (base : UInt256) : State :=
  { baseLoopState input (baseSize input / 32) base with pc := UInt256.ofNat 2079 }

/-! ### The 16-entry window table `T[k] = base^k mod m`

Stored at memory words `0 … 15`, i.e. `[0x0000, 0x0200)`.  `T[0]` is
`mod(1, m)`, never the literal `1`: when `Esize = 0` the byte loop never runs
and `T[0]` is returned with no trailing `MULMOD`, so `m = 1` must give `0`. -/

def powTab (input : ByteArray) (base : UInt256) : Nat → UInt256
  | 0 => (1 : UInt256) % UInt256.ofNat (modulusValue input)
  | 1 => base
  | k + 2 =>
      UInt256.mulMod base (powTab input base (k + 1))
        (UInt256.ofNat (modulusValue input))

/-- Memory after `T[0] … T[k-1]` have been stored. -/
def tableMem (input : ByteArray) (base : UInt256) : Nat → ByteArray
  | 0 => (nonzeroState input).memory
  | k + 1 =>
      MachineState.writeBytes (tableMem input base k)
        (Data.Bytes.natToBytesPadded (powTab input base k).toNat 32) (32 * k)

/-- After `T[0]` and `T[1]`; the accumulator register is not yet on the stack. -/
def tableStartState (input : ByteArray) (base : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 2093
    stack := base :: wordFrame input
    memory := tableMem input base 2
    activeWords := UInt256.ofNat 2 }

/-- After `T[k]` has been stored, with `T[k]` still on the stack. -/
def tableState (input : ByteArray) (base : UInt256) (k pcv : Nat) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat pcv
    stack := powTab input base k :: base :: wordFrame input
    memory := tableMem input base (k + 1)
    activeWords := UInt256.ofNat (k + 1) }

/-! ### The unrolled exponent byte body -/

def sqStep (input : ByteArray) (x : UInt256) : UInt256 :=
  UInt256.mulMod x x (UInt256.ofNat (modulusValue input))

def sq4 (input : ByteArray) (x : UInt256) : UInt256 :=
  sqStep input (sqStep input (sqStep input (sqStep input x)))

/-- High nibble table entry.  The mask `0x1E0` keeps the `MLOAD` inside the
table for any `w`, but selects the right entry only because `w` comes from
`BYTE(0, ·)` and is therefore below `256`; that is a hypothesis, never an
inference from the mask. -/
def tabHi (input : ByteArray) (base w : UInt256) : UInt256 :=
  powTab input base (w.toNat / 16)

def tabLo (input : ByteArray) (base w : UInt256) : UInt256 :=
  powTab input base (w.toNat % 16)

def windowStep (input : ByteArray) (base w acc : UInt256) : UInt256 :=
  UInt256.mulMod
    (sq4 input
      (UInt256.mulMod (sq4 input acc) (tabHi input base w)
        (UInt256.ofNat (modulusValue input))))
    (tabLo input base w) (UInt256.ofNat (modulusValue input))

/-- Every state of the byte loop: the frame, then `base`, the live byte `w`,
the calldata pointer, and the accumulator. -/
def byteState (input : ByteArray) (base : UInt256) (i : Nat) (w acc : UInt256)
    (pcv : Nat) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat pcv
    stack := [acc, UInt256.ofNat (expOffset input + i), w, base] ++ wordFrame input
    memory := tableMem input base 16
    activeWords := UInt256.ofNat 16 }

def byteLoopState (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) : State := byteState input base i w acc 2220

/-- The state the appended body hands back to the unchanged exit block at
`0x029d`.  Every word-path run ends here or in the zero-modulus `RETURN`;
control never re-enters the big path, which is what makes the window table's
use of `[0x0000, 0x0200)` safe (constraint C1). -/
def wordExitState (input : ByteArray) (base acc : UInt256) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 669
    stack := [UInt256.ofNat (exponentSize input), acc, base] ++ wordFrame input
    memory := tableMem input base 16
    activeWords := UInt256.ofNat 16 }

/-! ### Loop guards, cut before the `JUMPI`

Cutting the block before the conditional jump makes the prefix certificate
unconditional and leaves the `ite` as the entire goal of a one-instruction
certificate, which `simp` orients directly. -/

def baseCond (input : ByteArray) (k : Nat) : UInt256 :=
  UInt256.isZero
    (UInt256.lt (UInt256.ofNat (basePtr input k))
      (UInt256.ofNat (expOffset input)))

def baseTestState (input : ByteArray) (k : Nat) (base : UInt256) : State :=
  { baseLoopState input k base with
    pc := UInt256.ofNat 2059
    stack := (2079 : UInt256) :: baseCond input k ::
      (baseLoopState input k base).stack }

def byteCond (input : ByteArray) (i : Nat) : UInt256 :=
  UInt256.isZero
    (UInt256.lt (UInt256.ofNat (expOffset input + i))
      (UInt256.ofNat (modulusOffset input)))

def byteTestState (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) : State :=
  { byteState input base i w acc 2228 with
    stack := (2300 : UInt256) :: byteCond input i ::
      (byteState input base i w acc 2228).stack }

/-! ### Pre-jump states

Terminal `JUMP`s are certified separately, so each loop back-edge and the exit
have a state with the destination already pushed. -/

def wordJumpState (input : ByteArray) : State :=
  { nonzeroState input with
    pc := UInt256.ofNat 542
    stack := (2019 : UInt256) :: wordFrame input }

def baseBackState (input : ByteArray) (k : Nat) (base : UInt256) : State :=
  { baseLoopState input (k + 1) base with
    pc := UInt256.ofNat 2078
    stack := (2051 : UInt256) :: (baseLoopState input (k + 1) base).stack }

def byteBackState (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) : State :=
  { byteLoopState input base (i + 1) w acc with
    pc := UInt256.ofNat 2299
    stack := (2220 : UInt256) :: (byteLoopState input base (i + 1) w acc).stack }

def wordExitJumpState (input : ByteArray) (base acc : UInt256) : State :=
  { wordExitState input base acc with
    pc := UInt256.ofNat 2309
    stack := (669 : UInt256) :: (wordExitState input base acc).stack }
/-! ## Straight-line paths

Every conditional jump and every terminal `JUMP` is cut into its own
one-instruction certificate.  The prefix certificates are then unconditional
and the jump goal is small enough for `simp` to orient directly. -/

def startPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 415 .JUMPDEST, opAt 416 (.Dup ⟨5, by decide⟩),
   opAt 417 .CALLDATALOAD, opAt 418 (.Dup ⟨3, by decide⟩),
   pushAt 419 1 32, opAt 420 .SUB, pushAt 421 1 3, opAt 422 .SHL,
   opAt 423 .SHR, opAt 424 (.Dup ⟨0, by decide⟩), pushAt 425 2 538,
   opAt 426 .JUMPI]

def zeroTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 427 (.Dup ⟨3, by decide⟩), pushAt 428 2 6144, opAt 429 .RETURN]

def zeroModulusPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  startPath ++ zeroTailPath

def startLoadPath := startPath.take 11
def startJumpPath := [opAt 426 .JUMPI]

def trampolinePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 430 .JUMPDEST, pushAt 431 2 2019]

def trampolineJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 432 .JUMP]

def newPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1495 .JUMPDEST, opAt 1496 (.Dup ⟨0, by decide⟩), pushAt 1497 0 0,
   opAt 1498 .NOT, opAt 1499 .MOD, pushAt 1500 1 1,
   opAt 1501 (.Dup ⟨2, by decide⟩), opAt 1502 (.Swap ⟨1, by decide⟩),
   opAt 1503 .ADDMOD, opAt 1504 (.Dup ⟨2, by decide⟩), pushAt 1505 1 31,
   opAt 1506 .AND, pushAt 1507 1 96, opAt 1508 .CALLDATALOAD,
   opAt 1509 (.Dup ⟨1, by decide⟩), pushAt 1510 1 32, opAt 1511 .SUB,
   pushAt 1512 1 3, opAt 1513 .SHL, opAt 1514 .SHR,
   opAt 1515 (.Dup ⟨3, by decide⟩), opAt 1516 (.Swap ⟨0, by decide⟩),
   opAt 1517 .MOD, opAt 1518 (.Swap ⟨0, by decide⟩), pushAt 1519 1 96,
   opAt 1520 .ADD]

def baseTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1521 .JUMPDEST, opAt 1522 (.Dup ⟨8, by decide⟩),
   opAt 1523 (.Dup ⟨1, by decide⟩), opAt 1524 .LT, opAt 1525 .ISZERO,
   pushAt 1526 2 2079]

def baseJumpiPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1527 .JUMPI]

def baseBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1528 (.Dup ⟨3, by decide⟩), opAt 1529 (.Dup ⟨3, by decide⟩),
   opAt 1530 (.Dup ⟨3, by decide⟩), opAt 1531 .MULMOD,
   opAt 1532 (.Dup ⟨4, by decide⟩), opAt 1533 (.Dup ⟨2, by decide⟩),
   opAt 1534 .CALLDATALOAD, opAt 1535 (.Swap ⟨0, by decide⟩),
   opAt 1536 (.Swap ⟨1, by decide⟩), opAt 1537 .ADDMOD,
   opAt 1538 (.Swap ⟨1, by decide⟩), opAt 1539 .POP, pushAt 1540 1 32,
   opAt 1541 .ADD, pushAt 1542 2 2051]

def baseLoopJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1543 .JUMP]

def tableInitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1544 .JUMPDEST, opAt 1545 .POP, opAt 1546 (.Swap ⟨0, by decide⟩),
   opAt 1547 .POP, opAt 1548 (.Dup ⟨1, by decide⟩), pushAt 1549 1 1,
   opAt 1550 .MOD, pushAt 1551 0 0, opAt 1552 .MSTORE,
   opAt 1553 (.Dup ⟨0, by decide⟩), pushAt 1554 1 32, opAt 1555 .MSTORE]

def table2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1556 (.Dup ⟨0, by decide⟩), opAt 1557 (.Dup ⟨2, by decide⟩),
   opAt 1558 (.Swap ⟨0, by decide⟩), opAt 1559 (.Dup ⟨2, by decide⟩),
   opAt 1560 .MULMOD, opAt 1561 (.Dup ⟨0, by decide⟩), pushAt 1562 1 64,
   opAt 1563 .MSTORE]

def tablePath3 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1564 (.Dup ⟨2, by decide⟩), opAt 1565 (.Swap ⟨0, by decide⟩),
   opAt 1566 (.Dup ⟨2, by decide⟩), opAt 1567 .MULMOD,
   opAt 1568 (.Dup ⟨0, by decide⟩), pushAt 1569 1 96, opAt 1570 .MSTORE]

def tablePath4 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1571 (.Dup ⟨2, by decide⟩), opAt 1572 (.Swap ⟨0, by decide⟩),
   opAt 1573 (.Dup ⟨2, by decide⟩), opAt 1574 .MULMOD,
   opAt 1575 (.Dup ⟨0, by decide⟩), pushAt 1576 1 128, opAt 1577 .MSTORE]

def tablePath5 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1578 (.Dup ⟨2, by decide⟩), opAt 1579 (.Swap ⟨0, by decide⟩),
   opAt 1580 (.Dup ⟨2, by decide⟩), opAt 1581 .MULMOD,
   opAt 1582 (.Dup ⟨0, by decide⟩), pushAt 1583 1 160, opAt 1584 .MSTORE]

def tablePath6 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1585 (.Dup ⟨2, by decide⟩), opAt 1586 (.Swap ⟨0, by decide⟩),
   opAt 1587 (.Dup ⟨2, by decide⟩), opAt 1588 .MULMOD,
   opAt 1589 (.Dup ⟨0, by decide⟩), pushAt 1590 1 192, opAt 1591 .MSTORE]

def tablePath7 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1592 (.Dup ⟨2, by decide⟩), opAt 1593 (.Swap ⟨0, by decide⟩),
   opAt 1594 (.Dup ⟨2, by decide⟩), opAt 1595 .MULMOD,
   opAt 1596 (.Dup ⟨0, by decide⟩), pushAt 1597 1 224, opAt 1598 .MSTORE]

def tablePath8 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1599 (.Dup ⟨2, by decide⟩), opAt 1600 (.Swap ⟨0, by decide⟩),
   opAt 1601 (.Dup ⟨2, by decide⟩), opAt 1602 .MULMOD,
   opAt 1603 (.Dup ⟨0, by decide⟩), pushAt 1604 2 256, opAt 1605 .MSTORE]

def tablePath9 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1606 (.Dup ⟨2, by decide⟩), opAt 1607 (.Swap ⟨0, by decide⟩),
   opAt 1608 (.Dup ⟨2, by decide⟩), opAt 1609 .MULMOD,
   opAt 1610 (.Dup ⟨0, by decide⟩), pushAt 1611 2 288, opAt 1612 .MSTORE]

def tablePath10 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1613 (.Dup ⟨2, by decide⟩), opAt 1614 (.Swap ⟨0, by decide⟩),
   opAt 1615 (.Dup ⟨2, by decide⟩), opAt 1616 .MULMOD,
   opAt 1617 (.Dup ⟨0, by decide⟩), pushAt 1618 2 320, opAt 1619 .MSTORE]

def tablePath11 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1620 (.Dup ⟨2, by decide⟩), opAt 1621 (.Swap ⟨0, by decide⟩),
   opAt 1622 (.Dup ⟨2, by decide⟩), opAt 1623 .MULMOD,
   opAt 1624 (.Dup ⟨0, by decide⟩), pushAt 1625 2 352, opAt 1626 .MSTORE]

def tablePath12 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1627 (.Dup ⟨2, by decide⟩), opAt 1628 (.Swap ⟨0, by decide⟩),
   opAt 1629 (.Dup ⟨2, by decide⟩), opAt 1630 .MULMOD,
   opAt 1631 (.Dup ⟨0, by decide⟩), pushAt 1632 2 384, opAt 1633 .MSTORE]

def tablePath13 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1634 (.Dup ⟨2, by decide⟩), opAt 1635 (.Swap ⟨0, by decide⟩),
   opAt 1636 (.Dup ⟨2, by decide⟩), opAt 1637 .MULMOD,
   opAt 1638 (.Dup ⟨0, by decide⟩), pushAt 1639 2 416, opAt 1640 .MSTORE]

def tablePath14 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1641 (.Dup ⟨2, by decide⟩), opAt 1642 (.Swap ⟨0, by decide⟩),
   opAt 1643 (.Dup ⟨2, by decide⟩), opAt 1644 .MULMOD,
   opAt 1645 (.Dup ⟨0, by decide⟩), pushAt 1646 2 448, opAt 1647 .MSTORE]

def tablePath15 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1648 (.Dup ⟨2, by decide⟩), opAt 1649 (.Swap ⟨0, by decide⟩),
   opAt 1650 (.Dup ⟨2, by decide⟩), opAt 1651 .MULMOD,
   opAt 1652 (.Dup ⟨0, by decide⟩), pushAt 1653 2 480, opAt 1654 .MSTORE]

def tableLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1655 .POP, pushAt 1656 0 0, opAt 1657 .MLOAD,
   opAt 1658 (.Dup ⟨7, by decide⟩), pushAt 1659 0 0,
   opAt 1660 (.Swap ⟨1, by decide⟩)]

def byteTestPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1661 .JUMPDEST, opAt 1662 (.Dup ⟨10, by decide⟩),
   opAt 1663 (.Dup ⟨2, by decide⟩), opAt 1664 .LT, opAt 1665 .ISZERO,
   pushAt 1666 2 2300]

def byteJumpiPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1667 .JUMPI]

def byteLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1668 (.Dup ⟨1, by decide⟩), opAt 1669 .CALLDATALOAD,
   pushAt 1670 0 0, opAt 1671 .BYTE, opAt 1672 (.Swap ⟨2, by decide⟩),
   opAt 1673 .POP]

def byteSq1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1674 (.Dup ⟨4, by decide⟩), opAt 1675 (.Swap ⟨0, by decide⟩),
   opAt 1676 (.Dup ⟨0, by decide⟩), opAt 1677 .MULMOD,
   opAt 1678 (.Dup ⟨4, by decide⟩), opAt 1679 (.Swap ⟨0, by decide⟩),
   opAt 1680 (.Dup ⟨0, by decide⟩), opAt 1681 .MULMOD,
   opAt 1682 (.Dup ⟨4, by decide⟩), opAt 1683 (.Swap ⟨0, by decide⟩),
   opAt 1684 (.Dup ⟨0, by decide⟩), opAt 1685 .MULMOD,
   opAt 1686 (.Dup ⟨4, by decide⟩), opAt 1687 (.Swap ⟨0, by decide⟩),
   opAt 1688 (.Dup ⟨0, by decide⟩), opAt 1689 .MULMOD]

def byteHiPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1690 (.Dup ⟨2, by decide⟩), pushAt 1691 1 1, opAt 1692 .SHL,
   pushAt 1693 2 480, opAt 1694 .AND, opAt 1695 .MLOAD,
   opAt 1696 (.Dup ⟨5, by decide⟩), opAt 1697 (.Swap ⟨1, by decide⟩),
   opAt 1698 .MULMOD]

def byteSq2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1699 (.Dup ⟨4, by decide⟩), opAt 1700 (.Swap ⟨0, by decide⟩),
   opAt 1701 (.Dup ⟨0, by decide⟩), opAt 1702 .MULMOD,
   opAt 1703 (.Dup ⟨4, by decide⟩), opAt 1704 (.Swap ⟨0, by decide⟩),
   opAt 1705 (.Dup ⟨0, by decide⟩), opAt 1706 .MULMOD,
   opAt 1707 (.Dup ⟨4, by decide⟩), opAt 1708 (.Swap ⟨0, by decide⟩),
   opAt 1709 (.Dup ⟨0, by decide⟩), opAt 1710 .MULMOD,
   opAt 1711 (.Dup ⟨4, by decide⟩), opAt 1712 (.Swap ⟨0, by decide⟩),
   opAt 1713 (.Dup ⟨0, by decide⟩), opAt 1714 .MULMOD]

def byteLoPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1715 (.Dup ⟨2, by decide⟩), pushAt 1716 1 5, opAt 1717 .SHL,
   pushAt 1718 2 480, opAt 1719 .AND, opAt 1720 .MLOAD,
   opAt 1721 (.Dup ⟨5, by decide⟩), opAt 1722 (.Swap ⟨1, by decide⟩),
   opAt 1723 .MULMOD]

def byteAdvancePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1724 (.Swap ⟨0, by decide⟩), pushAt 1725 1 1, opAt 1726 .ADD,
   opAt 1727 (.Swap ⟨0, by decide⟩), pushAt 1728 2 2220]

def byteLoopJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1729 .JUMP]

def byteExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1730 .JUMPDEST, opAt 1731 (.Swap ⟨0, by decide⟩), opAt 1732 .POP,
   opAt 1733 (.Swap ⟨0, by decide⟩), opAt 1734 .POP,
   opAt 1735 (.Dup ⟨4, by decide⟩), pushAt 1736 2 669]

def byteExitJumpPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1737 .JUMP]

/-! ## Jump destinations

`Artifact.isValidJumpDest_index i` produces the claim at `Artifact.instructionPC
i`; the goal carries the byte literal.  Bridging through the `pc*` chain avoids
re-assembling the prefix, which for indices past 1500 costs seconds each. -/

@[simp] theorem jump538 :
    Decode.isValidJumpDest submissionBytecode 538 = true :=
  Artifact.isValidJumpDest_index 430 (by rfl)

@[simp] theorem jump2019 :
    Decode.isValidJumpDest submissionBytecode 2019 = true := by
  have h := Artifact.isValidJumpDest_index 1495 (by rfl)
  rwa [show Artifact.instructionPC 1495 = 2019 from WordPC.pc1495] at h

@[simp] theorem jump2051 :
    Decode.isValidJumpDest submissionBytecode 2051 = true := by
  have h := Artifact.isValidJumpDest_index 1521 (by rfl)
  rwa [show Artifact.instructionPC 1521 = 2051 from WordPC.pc1521] at h

@[simp] theorem jump2079 :
    Decode.isValidJumpDest submissionBytecode 2079 = true := by
  have h := Artifact.isValidJumpDest_index 1544 (by rfl)
  rwa [show Artifact.instructionPC 1544 = 2079 from WordPC.pc1544] at h

@[simp] theorem jump2220 :
    Decode.isValidJumpDest submissionBytecode 2220 = true := by
  have h := Artifact.isValidJumpDest_index 1661 (by rfl)
  rwa [show Artifact.instructionPC 1661 = 2220 from WordPC.pc1661] at h

@[simp] theorem jump2300 :
    Decode.isValidJumpDest submissionBytecode 2300 = true := by
  have h := Artifact.isValidJumpDest_index 1730 (by rfl)
  rwa [show Artifact.instructionPC 1730 = 2300 from WordPC.pc1730] at h

@[simp] theorem jump669 :
    Decode.isValidJumpDest submissionBytecode 669 = true :=
  Artifact.isValidJumpDest_index 536 (by rfl)

/-! ## Word-level arithmetic used by the entry block -/

theorem land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = (a.toNat &&& b.toNat) := by
  cases a with | mk a =>
  cases b with | mk b =>
  simp only [UInt256.land, UInt256.toNat]
  unfold Fin.land
  simp only
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left a.isLt)

theorem land_31_ofNat (n : Nat) :
    UInt256.land 31 (UInt256.ofNat n) = UInt256.ofNat (n % 32) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [land_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat]
  rw [show (31 : UInt256).toNat = 2 ^ 5 - 1 by decide, Nat.and_comm,
    Nat.and_two_pow_sub_one_eq_mod]
  have h : (n % 2 ^ 256) % 2 ^ 5 = n % 2 ^ 5 :=
    Nat.mod_mod_of_dvd n (by norm_num [pow_dvd_pow 2 (by norm_num : 5 ≤ 256)])
  rw [show (2:Nat) ^ 5 = 32 by norm_num] at h
  rw [h, Nat.mod_eq_of_lt (by omega : n % 32 < 2 ^ 256)]

/-- `SHR` by 256 or more is `0`.  `Bytes.shiftRight_readWord` carries
`0 < width` and does not cover this, but it is exactly the `bsize mod 32 = 0`
case of the base loop. -/
theorem shiftRight_full (x : UInt256) :
    UInt256.shiftRight x (UInt256.ofNat 256) = UInt256.ofNat 0 := by
  unfold UInt256.shiftRight
  rw [if_pos (by rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat]
  rfl

theorem mod_ofNat (value modulus : Nat) (hmodpos : 0 < modulus)
    (hmodlt : modulus < 2 ^ 256) (hvalue : value < 2 ^ 256) :
    UInt256.ofNat value % UInt256.ofNat modulus =
      UInt256.ofNat (value % modulus) := by
  change UInt256.mod (UInt256.ofNat value) (UInt256.ofNat modulus) = _
  unfold UInt256.mod
  have hmword : (UInt256.ofNat modulus).val.val ≠ 0 := by
    change (UInt256.ofNat modulus).toNat ≠ 0
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hmodlt]
    omega
  rw [if_neg hmword]
  apply Challenge.EvmProof.Word.word_ext
  change ((UInt256.ofNat value).val % (UInt256.ofNat modulus).val).val = _
  rw [Fin.val_mod]
  change (UInt256.ofNat value).toNat % (UInt256.ofNat modulus).toNat = _
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt hvalue, Nat.mod_eq_of_lt hmodlt,
    Nat.mod_eq_of_lt ((Nat.mod_lt _ hmodpos).trans hmodlt)]

theorem modulusValue_lt (input : ByteArray) (hword : modulusSize input ≤ 32) :
    modulusValue input < 2 ^ 256 := by
  refine lt_of_lt_of_le
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input
      (modulusOffset input) (modulusSize input)) ?_
  calc (256 : Nat) ^ modulusSize input ≤ 256 ^ 32 :=
        Nat.pow_le_pow_right (by norm_num) hword
    _ = 2 ^ 256 := by norm_num

theorem leadWidth_lt (input : ByteArray) : leadWidth input < 32 := by
  unfold leadWidth; omega

theorem lead_shift (input : ByteArray) :
    UInt256.shiftRight (MachineState.readWord input 96)
        (UInt256.ofNat ((32 - leadWidth input) * 8)) =
      UInt256.ofNat (Precompile.bytesToNatPadded input 96 (leadWidth input)) := by
  rcases Nat.eq_zero_or_pos (leadWidth input) with h | h
  · rw [h, Challenge.EvmProof.Bytes.bytesToNatPadded_zero_width,
      show (32 - 0) * 8 = 256 by norm_num, shiftRight_full]
  · exact Challenge.EvmProof.Bytes.shiftRight_readWord input 96
      (leadWidth input) h (le_of_lt (leadWidth_lt input))

/-! ## The window table in memory

`T[k]` lives at byte `32k`, so the sixteen writes are pairwise disjoint and a
read of word `k` peels every later write.  Memory `[0x0000, 0x0200)` is shared
with the big path's modulus buffer; see constraint C1 in the module header. -/

theorem readWord_tableMem (input : ByteArray) (base : UInt256) :
    ∀ (j k : Nat), k < j →
      MachineState.readWord (tableMem input base j) (32 * k) =
        powTab input base k := by
  intro j
  induction j with
  | zero => intro k hk; omega
  | succ j ih =>
      intro k hk
      rcases Nat.lt_or_ge k j with h | h
      · rw [tableMem,
          Challenge.EvmProof.Memory.readWord_writeBytes_disjoint _ _ _ _
            (Or.inl (by omega))]
        exact ih k h
      · have hkj : k = j := by omega
        subst hkj
        rw [tableMem]
        exact Challenge.EvmProof.Memory.readWord_writeWord _ _ _

/-! ### Window addressing

`(w << 1) & 0x1E0` and `(w << 5) & 0x1E0` land inside the table for *every*
`w`, but they select the intended entry only because `w < 256`, which holds
because `w` is produced by `BYTE(0, ·)`.  That bound is a hypothesis of every
lemma below; it is not implied by the mask. -/

theorem mask_hi_nat : ∀ n, n < 256 → 480 &&& (2 * n) = 32 * (n / 16) := by decide
theorem mask_lo_nat : ∀ n, n < 256 → 480 &&& (32 * n) = 32 * (n % 16) := by decide

/-- The table read never expands memory: the word path has already touched
sixteen words and `0x1E0 + 32 = 0x200`. -/
theorem activeWords_table (k : Nat) (hk : k ≤ 15) :
    MachineState.activeWordsAfter 16 (32 * k) 32 = 16 := by
  unfold MachineState.activeWordsAfter
  simp only [if_neg (by norm_num : ¬ (32 : Nat) = 0)]
  have h : (32 * k + 32 - 1) / 32 + 1 = k + 1 := by omega
  rw [h]
  simp only [Nat.max_def]
  split <;> omega

theorem shiftLeft_word (w : UInt256) (s : Nat) (hs : s < 256)
    (hres : w.toNat * 2 ^ s < 2 ^ 256) :
    UInt256.shiftLeft w (UInt256.ofNat s) = UInt256.ofNat (w.toNat * 2 ^ s) := by
  conv_lhs => rw [Challenge.EvmProof.Word.word_eq_ofNat_toNat w]
  exact Challenge.EvmProof.Word.shiftLeft_ofNat w.val.isLt hs hres

theorem maskHi (w : UInt256) (hw : w.toNat < 256) :
    UInt256.land 480 (UInt256.shiftLeft w 1) =
      UInt256.ofNat (32 * (w.toNat / 16)) := by
  rw [show (1 : UInt256) = UInt256.ofNat 1 from by decide,
    shiftLeft_word w 1 (by norm_num) (by norm_num; omega)]
  apply Challenge.EvmProof.Word.word_ext
  rw [land_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    show (480 : UInt256).toNat = 480 from by decide,
    Nat.mod_eq_of_lt (by norm_num; omega : w.toNat * 2 ^ 1 < 2 ^ 256),
    show w.toNat * 2 ^ 1 = 2 * w.toNat by ring, mask_hi_nat w.toNat hw,
    Nat.mod_eq_of_lt (by omega : 32 * (w.toNat / 16) < 2 ^ 256)]

theorem maskLo (w : UInt256) (hw : w.toNat < 256) :
    UInt256.land 480 (UInt256.shiftLeft w 5) =
      UInt256.ofNat (32 * (w.toNat % 16)) := by
  rw [show (5 : UInt256) = UInt256.ofNat 5 from by decide,
    shiftLeft_word w 5 (by norm_num) (by norm_num; omega)]
  apply Challenge.EvmProof.Word.word_ext
  rw [land_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    show (480 : UInt256).toNat = 480 from by decide,
    Nat.mod_eq_of_lt (by norm_num; omega : w.toNat * 2 ^ 5 < 2 ^ 256),
    show w.toNat * 2 ^ 5 = 32 * w.toNat by ring, mask_lo_nat w.toNat hw,
    Nat.mod_eq_of_lt (by omega : 32 * (w.toNat % 16) < 2 ^ 256)]

/-- The high-nibble table read, address and value together. -/
theorem tableRead_hi (input : ByteArray) (base w : UInt256) (hw : w.toNat < 256) :
    MachineState.readWord (tableMem input base 16)
        (UInt256.land 480 (UInt256.shiftLeft w 1)).toNat =
      tabHi input base w := by
  rw [maskHi w hw, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * (w.toNat / 16) < 2 ^ 256)]
  exact readWord_tableMem input base 16 (w.toNat / 16) (by omega)

theorem tableRead_lo (input : ByteArray) (base w : UInt256) (hw : w.toNat < 256) :
    MachineState.readWord (tableMem input base 16)
        (UInt256.land 480 (UInt256.shiftLeft w 5)).toNat =
      tabLo input base w := by
  rw [maskLo w hw, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * (w.toNat % 16) < 2 ^ 256)]
  exact readWord_tableMem input base 16 (w.toNat % 16) (by omega)

theorem activeWords_hi (w : UInt256) (hw : w.toNat < 256) :
    MachineState.activeWordsAfter 16
        (UInt256.land 480 (UInt256.shiftLeft w 1)).toNat 32 = 16 := by
  rw [maskHi w hw, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * (w.toNat / 16) < 2 ^ 256)]
  exact activeWords_table _ (by omega)

theorem activeWords_lo (w : UInt256) (hw : w.toNat < 256) :
    MachineState.activeWordsAfter 16
        (UInt256.land 480 (UInt256.shiftLeft w 5)).toNat 32 = 16 := by
  rw [maskLo w hw, Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 32 * (w.toNat % 16) < 2 ^ 256)]
  exact activeWords_table _ (by omega)

/-! `Artifact.lean` marks `word_toNat_land` as `simp`, so inside a block goal
the address appears as `UInt256.toNat 480 &&& …` rather than as a `land`.  The
primed forms are the shape the block certificates actually see. -/

theorem tableRead_hi' (input : ByteArray) (base w : UInt256) (hw : w.toNat < 256) :
    MachineState.readWord (tableMem input base 16)
        (UInt256.toNat 480 &&& (UInt256.shiftLeft w 1).toNat) =
      tabHi input base w := by
  rw [← land_toNat]
  exact tableRead_hi input base w hw

theorem tableRead_lo' (input : ByteArray) (base w : UInt256) (hw : w.toNat < 256) :
    MachineState.readWord (tableMem input base 16)
        (UInt256.toNat 480 &&& (UInt256.shiftLeft w 5).toNat) =
      tabLo input base w := by
  rw [← land_toNat]
  exact tableRead_lo input base w hw

theorem activeWords_hi' (w : UInt256) (hw : w.toNat < 256) :
    MachineState.activeWordsAfter 16
        (UInt256.toNat 480 &&& (UInt256.shiftLeft w 1).toNat) 32 = 16 := by
  rw [← land_toNat]
  exact activeWords_hi w hw

theorem activeWords_lo' (w : UInt256) (hw : w.toNat < 256) :
    MachineState.activeWordsAfter 16
        (UInt256.toNat 480 &&& (UInt256.shiftLeft w 5).toNat) 32 = 16 := by
  rw [← land_toNat]
  exact activeWords_lo w hw

/-! ## Entry from the dispatcher

Unchanged from the baseline: instruction indices 415–429 are inside the
`[412, 430)` range the merge leaves byte-identical.  The word path reads its
modulus *from calldata* here (`DUP6 CALLDATALOAD` at `0x0206`), never from
memory `0x0000` — which is what keeps the window table's use of
`[0x0000, 0x0200)` independent of the big path's modulus buffer (C1). -/

set_option linter.unusedSimpArgs false in
theorem run_startLoad (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock startLoadPath
      (Dispatch.wordEntryState input) = some (loadedState input) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hword
    (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - modulusSize input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - modulusSize input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have hslice := Challenge.EvmProof.Bytes.shiftRight_readWord input
    (modulusOffset input) (modulusSize input) hmsize hword
  have hmodOff : modulusOffset input < 2 ^ 256 := by
    simp only [modulusOffset, expOffset]
    omega
  have hshiftBound : (32 - modulusSize input) * 2 ^ 3 < 2 ^ 256 := by
    norm_num
    omega
  have hloaded :
      (MachineState.readWord input
        ((96 + baseSize input + exponentSize input) % 2 ^ 256)).shiftRight
          (((32 : UInt256) - UInt256.ofNat (modulusSize input)).shiftLeft 3) =
        UInt256.ofNat (modulusValue input) := by
    change (MachineState.readWord input
      ((modulusOffset input) % 2 ^ 256)).shiftRight _ = _
    rw [Nat.mod_eq_of_lt hmodOff,
      show (32 : UInt256) = UInt256.ofNat 32 by decide, hsub,
      show (3 : UInt256) = UInt256.ofNat 3 by decide, hshift, hslice]
    rfl
  norm_num at hloaded
  simp (config := { maxSteps := 300000 })
    [startLoadPath, startPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      Dispatch.wordEntryState, Main.headerState, initialState, loadedState,
      nonzeroState, wordFrame, callerRest,
      expOffset, modulusOffset, hsub, hshift, hslice,
      hmodOff, hshiftBound, UInt256.isTrue,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]
  rw [hloaded]

set_option linter.unusedSimpArgs false in
theorem run_startJump_nonzero (input : ByteArray)
    (hmodulus : 0 < modulusValue input)
    (hmodlt : modulusValue input < 2 ^ 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (nonzeroState input) := by
  have hmodNat : modulusValue input % 2 ^ 256 = modulusValue input :=
    Nat.mod_eq_of_lt hmodlt
  have hcondition : modulusValue input % 2 ^ 256 ≠ 0 := by
    rw [hmodNat]
    omega
  have h538 : (538 : UInt256).toNat = 538 := by decide
  have h538Word : (538 : UInt256) = UInt256.ofNat 538 := by decide
  simp [startJumpPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadedState, nonzeroState, wordFrame, callerRest, Dispatch.wordEntryState,
    Main.headerState, initialState, jump538, UInt256.isTrue,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmodNat, hcondition,
    hmodulus, h538, h538Word]
  simp_all [hcondition, h538, h538Word, jump538]

set_option linter.unusedSimpArgs false in
theorem run_startJump_zero (input : ByteArray)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock startJumpPath
      (loadedState input) = some (zeroDispatchState input) := by
  simp [startJumpPath, opAt, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadedState, zeroDispatchState, nonzeroState, wordFrame, callerRest,
    Dispatch.wordEntryState, Main.headerState, initialState,
    UInt256.isTrue, hmodulus,
    Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_zeroTail (input : ByteArray) (hvalid : ValidInput input)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock zeroTailPath
      (zeroDispatchState input) = some (zeroModulusFinalState input) := by
  rcases hvalid with ⟨_, _, _, hm⟩
  have hm' : modulusSize input < 2 ^ 256 := by omega
  have hmmod : modulusSize input % 2 ^ 256 = modulusSize input :=
    Nat.mod_eq_of_lt hm'
  have hmmodLiteral : modulusSize input %
      115792089237316195423570985008687907853269984665640564039457584007913129639936 =
        modulusSize input := by
    exact Nat.mod_eq_of_lt (by norm_num at hm'; exact hm')
  have h6144 : (6144 : UInt256).toNat = 6144 := by decide
  have h0 : (0 : UInt256).toNat = 0 := by decide
  simp [zeroTailPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    zeroDispatchState, zeroModulusFinalState, nonzeroState, wordFrame, callerRest,
    Dispatch.wordEntryState, Main.headerState, initialState,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmmod, hmmodLiteral,
    Nat.mod_eq_of_lt hm', h6144, h0, hmodulus]
  simp_all [State.activeWordsAfterUInt256, MachineState.activeWordsAfter]

/-! ## Trampoline and body entry -/

set_option linter.unusedSimpArgs false in
theorem run_trampoline (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock trampolinePath
      (nonzeroState input) = some (wordJumpState input) := by
  simp (config := { maxSteps := 40000 })
    [trampolinePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      nonzeroState, wordJumpState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_trampolineJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock trampolineJumpPath
      (wordJumpState input) = some (wordBodyState input) := by
  have h2019 : (2019 : UInt256).toNat = 2019 := by decide
  have h2019Word : (2019 : UInt256) = UInt256.ofNat 2019 := by decide
  simp (config := { maxSteps := 40000 })
    [trampolineJumpPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordJumpState, wordBodyState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      Challenge.EvmProof.Word.word_toNat_ofNat, h2019, jump2019, h2019Word]

set_option linter.unusedSimpArgs false in
theorem run_new (input : ByteArray) (hvalid : ValidInput input)
    (hword : modulusSize input ≤ 32) (hmodpos : 0 < modulusValue input) :
    Challenge.EvmProof.Stepper.runLocatedBlock newPath (wordBodyState input) =
      some (baseLoopState input 0 (baseInit input)) := by
  rcases hvalid with ⟨_, hb, he, hm⟩
  have hmodlt : modulusValue input < 2 ^ 256 := modulusValue_lt input hword
  have hlw : leadWidth input < 32 := leadWidth_lt input
  have h32Word : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h3Word : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have h96 : (96 : UInt256).toNat = 96 := by decide
  have h96Word : (96 : UInt256) = UInt256.ofNat 96 := by decide
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat
    (by omega : leadWidth input ≤ 32) (by norm_num : 32 < 2 ^ 256)
  have hshift :
      UInt256.shiftLeft (UInt256.ofNat (32 - leadWidth input))
          (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - leadWidth input) * 8) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat] <;>
      norm_num [Nat.shiftLeft_eq] <;> omega
  have hlead := lead_shift input
  have hmodEq := mod_ofNat (Precompile.bytesToNatPadded input 96 (leadWidth input))
    (modulusValue input) hmodpos hmodlt
    (Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow input 96 (leadWidth input)
      |>.trans_le (by
        calc (256 : Nat) ^ leadWidth input ≤ 256 ^ 32 :=
              Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 2 ^ 256 := by norm_num))
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  have hlwDef : baseSize input % 32 = leadWidth input := rfl
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 96) (b := leadWidth input) (by omega)
  simp (config := { maxSteps := 400000 })
    [newPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordBodyState, baseLoopState, basePtr, baseInit, radixWord,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, land_31_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      h32Word, h3Word, h96, h96Word, hsub, hshift, hlead, hmodEq, hadd,
      hzeroRaw, hlwDef]

/-! ## Word-at-a-time base reduction -/

set_option linter.unusedSimpArgs false in
theorem run_baseTest (input : ByteArray) (k : Nat) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseTestPath
      (baseLoopState input k base) = some (baseTestState input k base) := by
  simp (config := { maxSteps := 200000 })
    [baseTestPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseLoopState, baseTestState, baseCond, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem baseCond_lt (input : ByteArray) (k : Nat)
    (hlt : basePtr input k < expOffset input)
    (hexp : expOffset input < 2 ^ 256) :
    baseCond input k = UInt256.ofNat 0 := by
  unfold baseCond UInt256.lt
  rw [if_pos (by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : basePtr input k < 2 ^ 256),
      Nat.mod_eq_of_lt hexp]
    exact hlt)]
  unfold UInt256.isZero
  rw [if_neg (by rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)]

theorem baseCond_ge (input : ByteArray) (k : Nat)
    (hge : expOffset input ≤ basePtr input k)
    (hptr : basePtr input k < 2 ^ 256) :
    baseCond input k = UInt256.ofNat 1 := by
  unfold baseCond UInt256.lt
  rw [if_neg (by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hptr,
      Nat.mod_eq_of_lt (by omega : expOffset input < 2 ^ 256)]
    omega)]
  unfold UInt256.isZero
  rw [if_pos (by rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)]

set_option linter.unusedSimpArgs false in
theorem run_baseJumpi_continue (input : ByteArray) (k : Nat) (base : UInt256)
    (hcond : baseCond input k = UInt256.ofNat 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseJumpiPath
      (baseTestState input k base) = some (baseBodyState input k base) := by
  simp (config := { maxSteps := 100000 })
    [baseJumpiPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseTestState, baseBodyState, baseLoopState, nonzeroState, wordFrame,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, hcond, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_baseJumpi_exit (input : ByteArray) (base : UInt256)
    (hcond : baseCond input (baseSize input / 32) = UInt256.ofNat 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseJumpiPath
      (baseTestState input (baseSize input / 32) base) =
        some (baseExitState input base) := by
  have h2079 : (2079 : UInt256).toNat = 2079 := by decide
  have h2079Word : (2079 : UInt256) = UInt256.ofNat 2079 := by decide
  simp (config := { maxSteps := 100000 })
    [baseJumpiPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseTestState, baseExitState, baseLoopState, nonzeroState, wordFrame,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, hcond, h2079, h2079Word, jump2079,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem basePtr_lt (input : ByteArray) (k : Nat) (hb : baseSize input ≤ 1024)
    (hk : k ≤ baseSize input / 32) : basePtr input k < 2 ^ 256 := by
  have h : leadWidth input < 32 := leadWidth_lt input
  have : basePtr input k = 96 + leadWidth input + 32 * k := rfl
  omega

set_option linter.unusedSimpArgs false in
theorem run_baseBody (input : ByteArray) (k : Nat) (base : UInt256)
    (hb : baseSize input ≤ 1024) (hk : k < baseSize input / 32) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseBodyPath
      (baseBodyState input k base) =
        some (baseBackState input k (hornerStep input k base)) := by
  have hval : basePtr input k = 96 + leadWidth input + 32 * k := rfl
  have hlw : leadWidth input < 32 := leadWidth_lt input
  have hkb : 32 * k < baseSize input := by omega
  have hptr : basePtr input k < 2 ^ 256 := basePtr_lt input k hb (by omega)
  have hptrSucc : 32 + basePtr input k = basePtr input (k + 1) := by
    show 32 + (96 + leadWidth input + 32 * k) = 96 + leadWidth input + 32 * (k + 1)
    omega
  have hcall : (UInt256.ofNat (basePtr input k)).toNat = basePtr input k := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hptr]
  have hadd32 := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 32) (b := basePtr input k) (by omega)
  have h32Word : (32 : UInt256) = UInt256.ofNat 32 := by decide
  simp (config := { maxSteps := 300000 })
    [baseBodyPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseBodyState, baseBackState, baseLoopState, hornerStep,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, h32Word, hcall, hadd32, hptrSucc,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_baseLoopJump (input : ByteArray) (k : Nat) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock baseLoopJumpPath
      (baseBackState input k base) = some (baseLoopState input (k + 1) base) := by
  have h2051 : (2051 : UInt256).toNat = 2051 := by decide
  have h2051Word : (2051 : UInt256) = UInt256.ofNat 2051 := by decide
  simp (config := { maxSteps := 100000 })
    [baseLoopJumpPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseBackState, baseLoopState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      h2051, h2051Word, jump2051,
      Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## Building the 16-entry window table -/

set_option linter.unusedSimpArgs false in
theorem run_tableInit (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tableInitPath
      (baseExitState input base) = some (tableStartState input base) := by
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have h32 : (32 : UInt256).toNat = 32 := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 300000 })
    [tableInitPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      baseExitState, baseLoopState, tableStartState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, h0, h32, hzeroRaw,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]
set_option linter.unusedSimpArgs false in
theorem run_table2 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock table2Path
      (tableStartState input base) = some (tableState input base 2 2102) := by
  have haddr : (64 : UInt256).toNat = 64 := by decide
  simp (config := { maxSteps := 300000 })
    [table2Path, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableStartState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table3 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath3
      (tableState input base 2 2102) = some (tableState input base 3 2110) := by
  have haddr : (96 : UInt256).toNat = 96 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath3, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table4 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath4
      (tableState input base 3 2110) = some (tableState input base 4 2118) := by
  have haddr : (128 : UInt256).toNat = 128 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath4, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table5 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath5
      (tableState input base 4 2118) = some (tableState input base 5 2126) := by
  have haddr : (160 : UInt256).toNat = 160 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath5, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table6 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath6
      (tableState input base 5 2126) = some (tableState input base 6 2134) := by
  have haddr : (192 : UInt256).toNat = 192 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath6, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table7 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath7
      (tableState input base 6 2134) = some (tableState input base 7 2142) := by
  have haddr : (224 : UInt256).toNat = 224 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath7, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table8 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath8
      (tableState input base 7 2142) = some (tableState input base 8 2151) := by
  have haddr : (256 : UInt256).toNat = 256 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath8, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table9 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath9
      (tableState input base 8 2151) = some (tableState input base 9 2160) := by
  have haddr : (288 : UInt256).toNat = 288 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath9, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table10 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath10
      (tableState input base 9 2160) = some (tableState input base 10 2169) := by
  have haddr : (320 : UInt256).toNat = 320 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath10, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table11 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath11
      (tableState input base 10 2169) = some (tableState input base 11 2178) := by
  have haddr : (352 : UInt256).toNat = 352 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath11, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table12 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath12
      (tableState input base 11 2178) = some (tableState input base 12 2187) := by
  have haddr : (384 : UInt256).toNat = 384 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath12, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table13 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath13
      (tableState input base 12 2187) = some (tableState input base 13 2196) := by
  have haddr : (416 : UInt256).toNat = 416 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath13, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table14 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath14
      (tableState input base 13 2196) = some (tableState input base 14 2205) := by
  have haddr : (448 : UInt256).toNat = 448 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath14, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_table15 (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tablePath15
      (tableState input base 14 2205) = some (tableState input base 15 2214) := by
  have haddr : (480 : UInt256).toNat = 480 := by decide
  simp (config := { maxSteps := 300000 })
    [tablePath15, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, tableState, tableMem, powTab,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, haddr,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_tableLoad (input : ByteArray) (base : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock tableLoadPath
      (tableState input base 15 2214) =
        some (byteLoopState input base 0 0 (powTab input base 0)) := by
  have h0 : (0 : UInt256).toNat = 0 := by decide
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  have hread : MachineState.readWord (tableMem input base 16) 0 =
      powTab input base 0 := by
    simpa using readWord_tableMem input base 16 0 (by norm_num)
  simp (config := { maxSteps := 300000 })
    [tableLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      tableState, byteLoopState, byteState,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, h0, hzeroRaw, hread,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## The exponent byte loop -/

set_option linter.unusedSimpArgs false in
theorem run_byteTest (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteTestPath
      (byteLoopState input base i w acc) =
        some (byteTestState input base i w acc) := by
  simp (config := { maxSteps := 200000 })
    [byteTestPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteLoopState, byteState, byteTestState, byteCond,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      Challenge.EvmProof.Word.word_toNat_ofNat]

theorem byteCond_lt (input : ByteArray) (i : Nat)
    (hi : i < exponentSize input) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) :
    byteCond input i = UInt256.ofNat 0 := by
  have hexp : expOffset input = 96 + baseSize input := rfl
  have hmod : modulusOffset input = expOffset input + exponentSize input := rfl
  unfold byteCond UInt256.lt
  rw [if_pos (by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : expOffset input + i < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : modulusOffset input < 2 ^ 256)]
    omega)]
  unfold UInt256.isZero
  rw [if_neg (by rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)]

theorem byteCond_ge (input : ByteArray) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) :
    byteCond input (exponentSize input) = UInt256.ofNat 1 := by
  have hexp : expOffset input = 96 + baseSize input := rfl
  have hmod : modulusOffset input = expOffset input + exponentSize input := rfl
  unfold byteCond UInt256.lt
  rw [if_neg (by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : expOffset input + exponentSize input < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : modulusOffset input < 2 ^ 256)]
    omega)]
  unfold UInt256.isZero
  rw [if_pos (by rw [Challenge.EvmProof.Word.word_toNat_ofNat]; norm_num)]

set_option linter.unusedSimpArgs false in
theorem run_byteJumpi_continue (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) (hcond : byteCond input i = UInt256.ofNat 0) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteJumpiPath
      (byteTestState input base i w acc) =
        some (byteState input base i w acc 2229) := by
  simp (config := { maxSteps := 100000 })
    [byteJumpiPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteTestState, byteState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, hcond, Challenge.EvmProof.Word.word_toNat_ofNat]

/-! The only way out of the byte loop.  It lands at `0x08fc`, which falls
through to the `JUMP` to `0x029d`; every continuation from there is a `RETURN`.
This is the lemma constraint C1 rests on. -/
set_option linter.unusedSimpArgs false in
theorem run_byteJumpi_exit (input : ByteArray) (base : UInt256)
    (w acc : UInt256)
    (hcond : byteCond input (exponentSize input) = UInt256.ofNat 1) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteJumpiPath
      (byteTestState input base (exponentSize input) w acc) =
        some (byteState input base (exponentSize input) w acc 2300) := by
  have h2300 : (2300 : UInt256).toNat = 2300 := by decide
  have h2300Word : (2300 : UInt256) = UInt256.ofNat 2300 := by decide
  simp (config := { maxSteps := 100000 })
    [byteJumpiPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteTestState, byteState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      UInt256.isTrue, hcond, h2300, h2300Word, jump2300,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteLoad (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteLoadPath
      (byteState input base i w acc 2229) =
        some (byteState input base i (byteWord input (expOffset input + i))
          acc 2235) := by
  have hexp : expOffset input = 96 + baseSize input := rfl
  have hoff : (UInt256.ofNat (expOffset input + i)).toNat = expOffset input + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : expOffset input + i < 2 ^ 256)]
  have hzeroRaw : ({ val := 0 } : UInt256) = 0 := by decide
  simp (config := { maxSteps := 200000 })
    [byteLoadPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, byteWord, Accessors.calldataByteValue,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, hoff, hzeroRaw,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteSq1 (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteSq1Path
      (byteState input base i w acc 2235) =
        some (byteState input base i w (sq4 input acc) 2251) := by
  simp (config := { maxSteps := 300000 })
    [byteSq1Path, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, sq4, sqStep, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteSq2 (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteSq2Path
      (byteState input base i w acc 2263) =
        some (byteState input base i w (sq4 input acc) 2279) := by
  simp (config := { maxSteps := 300000 })
    [byteSq2Path, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, sq4, sqStep, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteHi (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) (hw : w.toNat < 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteHiPath
      (byteState input base i w acc 2251) =
        some (byteState input base i w
          (UInt256.mulMod acc (tabHi input base w)
            (UInt256.ofNat (modulusValue input))) 2263) := by
  have hread := tableRead_hi' input base w hw
  have hactive := activeWords_hi' w hw
  simp (config := { maxSteps := 300000 })
    [byteHiPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteLo (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) (hw : w.toNat < 256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteLoPath
      (byteState input base i w acc 2279) =
        some (byteState input base i w
          (UInt256.mulMod acc (tabLo input base w)
            (UInt256.ofNat (modulusValue input))) 2291) := by
  have hread := tableRead_lo' input base w hw
  have hactive := activeWords_lo' w hw
  simp (config := { maxSteps := 300000 })
    [byteLoPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, hread, hactive,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteAdvance (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) (hb : baseSize input ≤ 1024)
    (he : exponentSize input ≤ 1024) (hi : i < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteAdvancePath
      (byteState input base i w acc 2291) =
        some (byteBackState input base i w acc) := by
  have hexp : expOffset input = 96 + baseSize input := rfl
  have hsucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1) (b := expOffset input + i) (by omega)
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hstep : 1 + (expOffset input + i) = expOffset input + (i + 1) := by omega
  simp (config := { maxSteps := 200000 })
    [byteAdvancePath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, byteBackState, byteLoopState,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, hone, hsucc, hstep,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteLoopJump (input : ByteArray) (base : UInt256) (i : Nat)
    (w acc : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteLoopJumpPath
      (byteBackState input base i w acc) =
        some (byteLoopState input base (i + 1) w acc) := by
  have h2220 : (2220 : UInt256).toNat = 2220 := by decide
  have h2220Word : (2220 : UInt256) = UInt256.ofNat 2220 := by decide
  simp (config := { maxSteps := 100000 })
    [byteLoopJumpPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteBackState, byteLoopState, byteState, nonzeroState, wordFrame,
      callerRest, Dispatch.wordEntryState, Main.headerState, initialState,
      h2220, h2220Word, jump2220,
      Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteExit (input : ByteArray) (base : UInt256) (w acc : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteExitPath
      (byteState input base (exponentSize input) w acc 2300) =
        some (wordExitJumpState input base acc) := by
  simp (config := { maxSteps := 200000 })
    [byteExitPath, opAt, pushAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      byteState, wordExitJumpState, wordExitState,
      nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      List.exchange, Challenge.EvmProof.Word.word_toNat_ofNat]

set_option linter.unusedSimpArgs false in
theorem run_byteExitJump (input : ByteArray) (base acc : UInt256) :
    Challenge.EvmProof.Stepper.runLocatedBlock byteExitJumpPath
      (wordExitJumpState input base acc) =
        some (wordExitState input base acc) := by
  have h669 : (669 : UInt256).toNat = 669 := by decide
  have h669Word : (669 : UInt256) = UInt256.ofNat 669 := by decide
  simp (config := { maxSteps := 100000 })
    [byteExitJumpPath, opAt,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      wordExitJumpState, wordExitState, nonzeroState, wordFrame, callerRest,
      Dispatch.wordEntryState, Main.headerState, initialState,
      h669, h669Word, jump669,
      Challenge.EvmProof.Word.word_toNat_ofNat]

/-! ## The zero-modulus exit

`modulusValue = 0` returns `0` of the declared width from `0x0219` without
entering the appended body at all, so the window table is never built on this
path. -/

def gasSteps_start (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : 0 < modulusValue input) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (nonzeroState input) := by
  have hmodlt : modulusValue input < 2 ^ 256 := modulusValue_lt input hword
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startLoadPath rfl rfl
        (run_startLoad input hvalid hmsize hword) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startJumpPath rfl rfl
        (run_startJump_nonzero input hmodulus hmodlt) rfl
        deployAddress_not_precompile)

def gasSteps_zeroModulus (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (Dispatch.wordEntryState input)
      (zeroModulusFinalState input) := by
  exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startLoadPath rfl rfl
        (run_startLoad input hvalid hmsize hword) rfl
        deployAddress_not_precompile).trans <|
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka startJumpPath rfl rfl
        (run_startJump_zero input hmodulus) rfl
        deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka zeroTailPath rfl rfl
        (run_zeroTail input hvalid hmodulus) rfl deployAddress_not_precompile)

def gasSteps_zeroModulus_total (input : ByteArray) (hvalid : ValidInput input)
    (hmsize : 0 < modulusSize input) (hword : modulusSize input ≤ 32)
    (hmodulus : modulusValue input = 0) :
    Challenge.EvmProof.GasSteps (initialState submissionBytecode input 0)
      (zeroModulusFinalState input) :=
  ((Main.gasSteps_header input hvalid).trans
    (Dispatch.gasSteps_wordEntry input hvalid hmsize hword)).trans
      (gasSteps_zeroModulus input hvalid hmsize hword hmodulus)

@[simp] theorem zeroModulusFinalState_isDone (input : ByteArray) :
    (zeroModulusFinalState input).isDone = true := by
  rfl

theorem zeroModulusFinalState_result (input : ByteArray)
    (hmsize : 0 < modulusSize input) (hmodulus : modulusValue input = 0) :
    (zeroModulusFinalState input).toResult = .returned (spec input) := by
  rw [show (zeroModulusFinalState input).toResult =
      .returned (Precompile.natToBytes 0 (modulusSize input)) by
    simp [zeroModulusFinalState, Algorithm.zeroBytes]]
  have hmodulus' :
      Precompile.bytesToNatPadded input
        (96 + baseSize input + exponentSize input) (modulusSize input) = 0 := by
    simpa [modulusValue, modulusOffset, expOffset, Nat.add_assoc] using hmodulus
  simp [spec, Nat.ne_of_gt hmsize, hmodulus', Precompile.modPow]

/-! ## Entering the appended body -/

def gasSteps_enterBody (input : ByteArray) :
    Challenge.EvmProof.GasSteps (nonzeroState input) (wordBodyState input) :=
  (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka trampolinePath rfl rfl
        (run_trampoline input) rfl deployAddress_not_precompile).trans
    (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka trampolineJumpPath rfl rfl
        (run_trampolineJump input) rfl deployAddress_not_precompile)

end Challenge.Modexp.Submission.Proofs.Bytecode.Word
