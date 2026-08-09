import Challenge.Modexp.Submission.Proofs.Bytecode.Accessors
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Certified big-endian operand loading (word-at-a-time)

This module follows the emitted `loadBigEndian`, which walks the destination
**one 256-bit limb at a time** rather than one input byte at a time.  The
destination is modelled as little-endian 256-bit limbs, exactly as the later
modular-arithmetic helpers consume it.

## Control flow

The original region `[439, 512)` is now a size-preserving stub

    439 JUMPDEST ; 440 PUSH2 1784 ; 443 JUMP ; <unreachable filler>

and the body lives past the end of the program at PC 1784 (instruction index
1286).  Because the stub matches the original region in *both* byte count and
instruction count, no index or PC outside `[354, 411]` / `[440, 512)` moves on
account of this region; index 412 still sits at PC 512.  (Two sibling regions,
`addMaskedMod` and `modexpWord_exp`, are patched the same way in the same
artifact; `merged_layout.json` records the unchanged baseline index ranges
`[0,83) [262,353) [412,430) [536,1286)`.)

The body is five blocks:

| block     | indices     | PCs         | role                                  |
|-----------|-------------|-------------|---------------------------------------|
| `setup`   | 1286 - 1307 | 1784 - 1809 | build `end`, `K`, `at`; guard         |
| `loop`    | 1308 - 1324 | 1810 - 1829 | one full limb, then re-guard          |
| `tail`    | 1325 - 1331 | 1830 - 1839 | `r = len % 32`; skip if zero          |
| `partial` | 1332 - 1347 | 1840 - 1858 | the single partial top limb           |
| `exit`    | 1348 - 1355 | 1859 - 1866 | drop the frame and return             |

The working frame throughout is

    [at, K, end, off, len, dst, ret] ++ rest

with `at` the destination cursor, `end = dst + 32 * (len / 32)` the address one
past the last full limb (equivalently, the address of the partial limb), and
`K` chosen so that the source pointer for the limb at `at` is exactly `K - at`.

## Why the source pointer is `K - at`

Limb `k` sits at `dst + 32k` and holds the input bytes of significance
`32k .. 32k+31`, i.e. input byte indices `len-32(k+1) .. len-32k-1`.  A
big-endian `CALLDATALOAD` at `off + len - 32(k+1)` reads precisely those 32
bytes in precisely that order, so with

    K := off + len - 32 + dst      and      at := dst + 32k

we get `K - at = off + len - 32(k+1)` in the 256-bit ring.  The intermediate
`off + len - 32` may wrap when `len < 32`, but the loop body does not run in
that case, and ring subtraction makes the value exact whenever it is used
(`loadBase_sub_ptr`).

## Why the trip count is `loadRuns` and not `len / 32`

`gasSteps_loadBigEndian` carries no bound on `dst`, so `end = dst + 32*(len/32)`
may itself wrap.  When it does, the entry guard `at < end` is false and the
loop is skipped entirely -- the loader then writes at most the partial limb, at
`dst`.  `loadRuns` records that: it is `len / 32` when the destination range
fits in 256 bits and `0` otherwise.  Every caller does satisfy the fit
hypothesis, and `BigLoadCorrect.loadRuns_eq` retires the wrapped case there;
modelling it here is what lets the execution lemma keep its existing
signature.

**Why the two cases cannot both apply, and why a wrapped loop cannot re-enter.**
The `if fits then n else 0` shape is only sound when "does not fit" really does
imply zero iterations *and* a loop that is entered can never wrap.  Both hold
here, and neither is assumed:

* `not_lt_end_of_zero` proves the entry guard false from `loadRuns = 0`,
  covering *both* reasons it can be zero -- `len < 32`, and the wrapped case,
  where `32 * (len/32) < 2^256` forces `end.toNat = dst.toNat + 32*(len/32)
  - 2^256 < dst.toNat`.  So a wrapped destination never enters the loop.
* Conversely `lt_end_of_pos` needs `0 < loadRuns`, which via `loadRuns_fit`
  yields `dst.toNat + 32*(len/32) < 2^256`.  So *inside* the loop the cursor
  `dst + 32k` is unwrapped and strictly increasing for every `k ≤ loadRuns`
  (`loadPtr_toNat_of_le`), and the closing guard is decided by comparing two
  unwrapped naturals.  There is no `k` beyond `loadRuns` for which any
  certificate exists -- `run_loadLoop` demands `k + 1 < loadRuns` and
  `run_loadLoopLast` demands `k + 1 = loadRuns` -- so `gasSteps_loadFullLimbs`
  composes exactly `loadRuns` iterations and re-entry is not expressible.

`CALLDATALOAD` zero-pads past `calldatasize()`, exactly as the previous
byte-at-a-time reference's `byte(0, calldataload(off + i))` did, so short,
absent and past-the-end calldata need no side condition.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

/-! ## Instruction paths

Every entry below is checked against `Artifact.submissionInstructions` by `rfl`
inside `opAt` / `pushAt`, so this table cannot silently drift from the
regenerated artifact. -/

/-- The size-preserving stub left behind at the original entry point. -/
def loadStubPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 353 .JUMPDEST, pushAt 354 2 1784, opAt 355 .JUMP]

/-- `end := dst + (len - (len &&& 31))`, `K := off + len - 32 + dst`,
`at := dst`, then the entry guard `if ¬(at < end) goto tail`. -/
def loadSetupPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1286 .JUMPDEST, pushAt 1287 1 31, opAt 1288 (.Dup ⟨2, by decide⟩),
   opAt 1289 .AND, opAt 1290 (.Dup ⟨2, by decide⟩), opAt 1291 .SUB,
   opAt 1292 (.Dup ⟨3, by decide⟩), opAt 1293 .ADD,
   pushAt 1294 1 32, opAt 1295 (.Dup ⟨3, by decide⟩), opAt 1296 .SUB,
   opAt 1297 (.Dup ⟨2, by decide⟩), opAt 1298 .ADD,
   opAt 1299 (.Dup ⟨4, by decide⟩), opAt 1300 .ADD,
   opAt 1301 (.Dup ⟨4, by decide⟩), opAt 1302 (.Dup ⟨2, by decide⟩),
   opAt 1303 (.Dup ⟨1, by decide⟩), opAt 1304 .LT, opAt 1305 .ISZERO,
   pushAt 1306 2 1830, opAt 1307 .JUMPI]

/-- One full limb: `mstore(at, mload(at) ||| calldataload(K - at))`,
`at += 32`, then `if at < end goto loop`. -/
def loadLoopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1308 .JUMPDEST, opAt 1309 (.Dup ⟨0, by decide⟩),
   opAt 1310 (.Dup ⟨2, by decide⟩), opAt 1311 .SUB, opAt 1312 .CALLDATALOAD,
   opAt 1313 (.Dup ⟨1, by decide⟩), opAt 1314 .MLOAD, opAt 1315 .OR,
   opAt 1316 (.Dup ⟨1, by decide⟩), opAt 1317 .MSTORE,
   pushAt 1318 1 32, opAt 1319 .ADD,
   opAt 1320 (.Dup ⟨2, by decide⟩), opAt 1321 (.Dup ⟨1, by decide⟩),
   opAt 1322 .LT, pushAt 1323 2 1810, opAt 1324 .JUMPI]

/-- `r := len &&& 31`; `if r = 0 goto exit`. -/
def loadTailPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1325 .JUMPDEST, pushAt 1326 1 31, opAt 1327 (.Dup ⟨5, by decide⟩),
   opAt 1328 .AND, opAt 1329 .ISZERO, pushAt 1330 2 1859, opAt 1331 .JUMPI]

/-- The single partial top limb:
`mstore(at, mload(at) ||| (calldataload(off) >> (8 * (32 - r))))`. -/
def loadPartialPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1332 1 31, opAt 1333 (.Dup ⟨5, by decide⟩), opAt 1334 .AND,
   pushAt 1335 1 32, opAt 1336 .SUB, pushAt 1337 1 3, opAt 1338 .SHL,
   opAt 1339 (.Dup ⟨4, by decide⟩), opAt 1340 .CALLDATALOAD,
   opAt 1341 (.Swap ⟨0, by decide⟩), opAt 1342 .SHR,
   opAt 1343 (.Dup ⟨1, by decide⟩), opAt 1344 .MLOAD, opAt 1345 .OR,
   opAt 1346 (.Dup ⟨1, by decide⟩), opAt 1347 .MSTORE]

/-- Drop the seven-slot frame and jump to the return address. -/
def loadExitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1348 .JUMPDEST, opAt 1349 .POP, opAt 1350 .POP, opAt 1351 .POP,
   opAt 1352 .POP, opAt 1353 .POP, opAt 1354 .POP, opAt 1355 .JUMP]

/-! ## Index arithmetic retained for the serializer

`BigSerializeCorrect` and `BigBaseCorrect` consume this per-byte index
arithmetic to reason about the *serializer*, which still walks byte by byte.
It is therefore kept verbatim even though the loader no longer uses it. -/

def loadByte (calldata : ByteArray) (offset i : Nat) : UInt256 :=
  UInt256.byteAt ⟨0⟩ (MachineState.readWord calldata (offset + i))

def loadReverse (length i : Nat) : Nat := length - 1 - i

def loadLimb (length i : Nat) : Nat := loadReverse length i / 32

def loadShift (length i : Nat) : Nat := 8 * (loadReverse length i % 32)

def loadReverseWord (length : UInt256) (i : Nat) : UInt256 :=
  length - UInt256.ofNat 1 - UInt256.ofNat i

def loadLimbWord (length : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftRight (loadReverseWord length i) (UInt256.ofNat 5)

def loadShiftWord (length : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.land (loadReverseWord length i) (UInt256.ofNat 31))
    (UInt256.ofNat 3)

def loadAt (dst : UInt256) (length i : Nat) : UInt256 :=
  dst + UInt256.shiftLeft (loadLimbWord (UInt256.ofNat length) i)
    (UInt256.ofNat 5)

/-! ## The word-at-a-time model

Every definition below is written in the *syntactic* shape the stepper
produces, so the block certificates below close by reduction rather than by
ring reasoning on 256-bit words. -/

/-- Number of *full* limbs in a `length`-byte operand. -/
def fullLimbs (length : Nat) : Nat := length / 32

/-- The destination cursor after `k` full limbs.  Stated recursively because
the loop increments it with `PUSH1 32; ADD`, i.e. `32 + at`. -/
def loadPtr (dst : UInt256) : Nat → UInt256
  | 0 => dst
  | k + 1 => UInt256.ofNat 32 + loadPtr dst k

/-- `end := dst + (len - (len &&& 31))`: one past the last full limb, and
also the address of the partial limb. -/
def loadEndAddr (dst length : UInt256) : UInt256 :=
  dst + (length - UInt256.land length (UInt256.ofNat 31))

/-- `K := dst + (off + (len - 32))`, chosen so that the calldata pointer for
the limb at `at` is `K - at`. -/
def loadBase (offset length dst : UInt256) : UInt256 :=
  dst + (offset + (length - UInt256.ofNat 32))

/-- The 32-byte calldata window that becomes full limb `k`.  Stated at the
unwrapped byte offset; `loadBase_sub_ptr` discharges the 256-bit pointer
arithmetic inside the loop certificate, where the no-wrap hypothesis lives. -/
def loadWindow (calldata : ByteArray) (offset length : UInt256) (k : Nat) :
    UInt256 :=
  MachineState.readWord calldata
    (offset.toNat + (length.toNat - 32 * (k + 1)))

/-- The value the partial-limb block ORs in: the leading `len % 32` bytes of
the input, right-aligned. -/
def loadPartialValue (calldata : ByteArray) (offset length : UInt256) :
    UInt256 :=
  UInt256.shiftRight (MachineState.readWord calldata offset.toNat)
    (UInt256.ofNat ((32 - length.toNat % 32) * 8))

/-- Number of full-limb iterations the loop actually performs.

This is `len / 32` unless the destination range wraps the 256-bit address
space, in which case `end` wraps below `dst`, the entry guard `at < end`
fails immediately and the loop is skipped.  `gasSteps_loadBigEndian` carries
no bound on `dst`, so the wrapped case has to be modelled rather than
assumed away; `loadRuns_eq` retires it under the fit hypothesis that the
correctness layer does carry.

The `else 0` branch is *proved*, not assumed: `not_lt_end_of_zero` derives the
false entry guard from `loadRuns = 0` for both reasons it can be zero, and
`loadRuns_fit` shows a loop that is entered cannot wrap.  See the module
docstring. -/
def loadRuns (dst length : UInt256) : Nat :=
  if dst.toNat + 32 * fullLimbs length.toNat < 2 ^ 256 then
    fullLimbs length.toNat
  else 0

/-- Total number of destination limbs the loader writes: the full limbs, plus
the partial one when `len % 32 ≠ 0`. -/
def loadCount (dst length : UInt256) : Nat :=
  loadRuns dst length + (if length.toNat % 32 = 0 then 0 else 1)

/-- The word ORed into destination limb `k`. -/
def loadLimbValue (calldata : ByteArray) (offset length dst : UInt256)
    (k : Nat) : UInt256 :=
  if k < loadRuns dst length then loadWindow calldata offset length k
  else loadPartialValue calldata offset length

/-- Memory after `k` destination-limb writes.  Saturating: indices at or
beyond `loadCount` leave memory alone, which is what lets the exit states be
indexed by `len` while the loop is indexed by limbs -- and therefore what lets
`BigBaseCorrect.loadMemory_preserves_region` keep `iter ≤ length` verbatim. -/
def loadMemory (calldata : ByteArray) (offset length dst : UInt256) :
    Nat → ByteArray → ByteArray
  | 0, memory => memory
  | k + 1, memory =>
      let before := loadMemory calldata offset length dst k memory
      if k < loadCount dst length then
        MachineState.writeBytes before
          (Data.Bytes.natToBytesPadded
            (UInt256.lor (MachineState.readWord before (loadPtr dst k).toNat)
              (loadLimbValue calldata offset length dst k)).toNat 32)
          (loadPtr dst k).toNat
      else before

/-- Active words after `k` destination-limb writes: each write does one
`MLOAD` and one `MSTORE` at the same address. -/
def loadWords (active dst length : UInt256) : Nat → UInt256
  | 0 => active
  | k + 1 =>
      let before := loadWords active dst length k
      if k < loadCount dst length then
        UInt256.ofNat (MachineState.activeWordsAfter
          (UInt256.ofNat (MachineState.activeWordsAfter before.toNat
            (loadPtr dst k).toNat 32)).toNat (loadPtr dst k).toNat 32)
      else before

/-! ## States -/

/-- The caller's frame, at the original entry PC 439 (the stub). -/
def loadEntry (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 439
           stack := [offset, length, dst, returnDest] ++ rest }

/-- The same frame after the stub's `PUSH2; JUMP`, at the body entry PC 1784. -/
def loadBodyEntry (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1784
           stack := [offset, length, dst, returnDest] ++ rest }

/-- The seven-slot working frame `[at, K, end, off, len, dst, ret]`. -/
def loadFrame (offset length dst returnDest : UInt256) (k : Nat)
    (rest : List UInt256) : List UInt256 :=
  [loadPtr dst k, loadBase offset length dst, loadEndAddr dst length,
    offset, length, dst, returnDest] ++ rest

/-- The loop invariant at the loop head PC 1810, having written `k` limbs. -/
def loadLoop (s : State) (offset length dst : UInt256) (k : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1810
           stack := loadFrame offset length dst returnDest k rest
           memory := loadMemory s.executionEnv.calldata offset length dst k
             s.memory
           activeWords := loadWords s.activeWords dst length k }

/-- At the tail head PC 1830, with `k` limbs written. -/
def loadTailAt (s : State) (offset length dst : UInt256) (k : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { loadLoop s offset length dst k returnDest rest with
      pc := UInt256.ofNat 1830 }

/-- At PC 1840, the partial-limb block, all full limbs written. -/
def loadPartialEntry (s : State) (offset length dst : UInt256)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { loadLoop s offset length dst (loadRuns dst length) returnDest rest with
      pc := UInt256.ofNat 1840 }

/-- At the exit head PC 1859: the destination is fully written. -/
def loadDone (s : State) (offset length dst : UInt256)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { loadLoop s offset length dst length.toNat returnDest rest with
      pc := UInt256.ofNat 1859
      stack := loadFrame offset length dst returnDest (loadRuns dst length)
        rest }

/-- Back at the caller. -/
def loadReturned (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) : State :=
  { loadLoop s offset length dst length.toNat returnDest rest with
      pc := returnDest, stack := rest }

/-! ## List helpers used by `DUP` reduction -/

@[simp] private theorem listGetZero {α : Type} (head default : α)
    (tail : List α) :
    (head :: tail)[0]?.getD default = head := by
  rfl

@[simp] private theorem listGetElemZero {α : Type} (head : α)
    (tail : List α) :
    (head :: tail)[0]? = some head := by
  rfl

/-! ## PC tables

`instructionPC index = (assembleBytes (instructions.take index)).length`, so a
`decide` at index `i` re-assembles `i` instructions and a per-index table is
quadratic in the index.  The chain below pays that once per contiguous run and
then walks forward one instruction at a time: 73 entries in ~3.5 s rather than
~22 s, and it parallelises.

Every constant is machine-checked: a wrong PC makes the corresponding `pcStep`
fail to typecheck, so this table cannot drift from the artifact silently. -/

/-- Byte width of the instruction at an index (`0` past the end). -/
private def instrWidth (index : Nat) : Nat :=
  ((Artifact.submissionInstructions[index]?).map (fun i => i.bytes.length)).getD 0

private theorem instructionPC_succ (index : Nat) :
    Artifact.submissionArtifact.instructionPC (index + 1) =
      Artifact.submissionArtifact.instructionPC index + instrWidth index := by
  have hinstr : Artifact.submissionArtifact.instructions =
      Artifact.submissionInstructions := rfl
  unfold Challenge.EvmProof.ProgramArtifact.instructionPC instrWidth
  rw [hinstr, List.take_add_one, YulEvmCompiler.assembleBytes_append]
  simp [YulEvmCompiler.assembleBytes]
  cases Artifact.submissionInstructions[index]? <;> simp

private theorem pcStep {index pcv w : Nat}
    (hprev : Artifact.submissionArtifact.instructionPC index = pcv)
    (hw : instrWidth index = w) :
    Artifact.submissionArtifact.instructionPC (index + 1) = pcv + w := by
  rw [instructionPC_succ, hprev, hw]

@[simp] private theorem pc353 :
    Artifact.submissionArtifact.instructionPC 353 = 439 := by decide
@[simp] private theorem pc354 :
    Artifact.submissionArtifact.instructionPC 354 = 440 :=
  pcStep pc353 (by rfl)
@[simp] private theorem pc355 :
    Artifact.submissionArtifact.instructionPC 355 = 443 :=
  pcStep pc354 (by rfl)
@[simp] private theorem pc1286 :
    Artifact.submissionArtifact.instructionPC 1286 = 1784 := by decide
@[simp] private theorem pc1287 :
    Artifact.submissionArtifact.instructionPC 1287 = 1785 :=
  pcStep pc1286 (by rfl)
@[simp] private theorem pc1288 :
    Artifact.submissionArtifact.instructionPC 1288 = 1787 :=
  pcStep pc1287 (by rfl)
@[simp] private theorem pc1289 :
    Artifact.submissionArtifact.instructionPC 1289 = 1788 :=
  pcStep pc1288 (by rfl)
@[simp] private theorem pc1290 :
    Artifact.submissionArtifact.instructionPC 1290 = 1789 :=
  pcStep pc1289 (by rfl)
@[simp] private theorem pc1291 :
    Artifact.submissionArtifact.instructionPC 1291 = 1790 :=
  pcStep pc1290 (by rfl)
@[simp] private theorem pc1292 :
    Artifact.submissionArtifact.instructionPC 1292 = 1791 :=
  pcStep pc1291 (by rfl)
@[simp] private theorem pc1293 :
    Artifact.submissionArtifact.instructionPC 1293 = 1792 :=
  pcStep pc1292 (by rfl)
@[simp] private theorem pc1294 :
    Artifact.submissionArtifact.instructionPC 1294 = 1793 :=
  pcStep pc1293 (by rfl)
@[simp] private theorem pc1295 :
    Artifact.submissionArtifact.instructionPC 1295 = 1795 :=
  pcStep pc1294 (by rfl)
@[simp] private theorem pc1296 :
    Artifact.submissionArtifact.instructionPC 1296 = 1796 :=
  pcStep pc1295 (by rfl)
@[simp] private theorem pc1297 :
    Artifact.submissionArtifact.instructionPC 1297 = 1797 :=
  pcStep pc1296 (by rfl)
@[simp] private theorem pc1298 :
    Artifact.submissionArtifact.instructionPC 1298 = 1798 :=
  pcStep pc1297 (by rfl)
@[simp] private theorem pc1299 :
    Artifact.submissionArtifact.instructionPC 1299 = 1799 :=
  pcStep pc1298 (by rfl)
@[simp] private theorem pc1300 :
    Artifact.submissionArtifact.instructionPC 1300 = 1800 :=
  pcStep pc1299 (by rfl)
@[simp] private theorem pc1301 :
    Artifact.submissionArtifact.instructionPC 1301 = 1801 :=
  pcStep pc1300 (by rfl)
@[simp] private theorem pc1302 :
    Artifact.submissionArtifact.instructionPC 1302 = 1802 :=
  pcStep pc1301 (by rfl)
@[simp] private theorem pc1303 :
    Artifact.submissionArtifact.instructionPC 1303 = 1803 :=
  pcStep pc1302 (by rfl)
@[simp] private theorem pc1304 :
    Artifact.submissionArtifact.instructionPC 1304 = 1804 :=
  pcStep pc1303 (by rfl)
@[simp] private theorem pc1305 :
    Artifact.submissionArtifact.instructionPC 1305 = 1805 :=
  pcStep pc1304 (by rfl)
@[simp] private theorem pc1306 :
    Artifact.submissionArtifact.instructionPC 1306 = 1806 :=
  pcStep pc1305 (by rfl)
@[simp] private theorem pc1307 :
    Artifact.submissionArtifact.instructionPC 1307 = 1809 :=
  pcStep pc1306 (by rfl)
@[simp] private theorem pc1308 :
    Artifact.submissionArtifact.instructionPC 1308 = 1810 :=
  pcStep pc1307 (by rfl)
@[simp] private theorem pc1309 :
    Artifact.submissionArtifact.instructionPC 1309 = 1811 :=
  pcStep pc1308 (by rfl)
@[simp] private theorem pc1310 :
    Artifact.submissionArtifact.instructionPC 1310 = 1812 :=
  pcStep pc1309 (by rfl)
@[simp] private theorem pc1311 :
    Artifact.submissionArtifact.instructionPC 1311 = 1813 :=
  pcStep pc1310 (by rfl)
@[simp] private theorem pc1312 :
    Artifact.submissionArtifact.instructionPC 1312 = 1814 :=
  pcStep pc1311 (by rfl)
@[simp] private theorem pc1313 :
    Artifact.submissionArtifact.instructionPC 1313 = 1815 :=
  pcStep pc1312 (by rfl)
@[simp] private theorem pc1314 :
    Artifact.submissionArtifact.instructionPC 1314 = 1816 :=
  pcStep pc1313 (by rfl)
@[simp] private theorem pc1315 :
    Artifact.submissionArtifact.instructionPC 1315 = 1817 :=
  pcStep pc1314 (by rfl)
@[simp] private theorem pc1316 :
    Artifact.submissionArtifact.instructionPC 1316 = 1818 :=
  pcStep pc1315 (by rfl)
@[simp] private theorem pc1317 :
    Artifact.submissionArtifact.instructionPC 1317 = 1819 :=
  pcStep pc1316 (by rfl)
@[simp] private theorem pc1318 :
    Artifact.submissionArtifact.instructionPC 1318 = 1820 :=
  pcStep pc1317 (by rfl)
@[simp] private theorem pc1319 :
    Artifact.submissionArtifact.instructionPC 1319 = 1822 :=
  pcStep pc1318 (by rfl)
@[simp] private theorem pc1320 :
    Artifact.submissionArtifact.instructionPC 1320 = 1823 :=
  pcStep pc1319 (by rfl)
@[simp] private theorem pc1321 :
    Artifact.submissionArtifact.instructionPC 1321 = 1824 :=
  pcStep pc1320 (by rfl)
@[simp] private theorem pc1322 :
    Artifact.submissionArtifact.instructionPC 1322 = 1825 :=
  pcStep pc1321 (by rfl)
@[simp] private theorem pc1323 :
    Artifact.submissionArtifact.instructionPC 1323 = 1826 :=
  pcStep pc1322 (by rfl)
@[simp] private theorem pc1324 :
    Artifact.submissionArtifact.instructionPC 1324 = 1829 :=
  pcStep pc1323 (by rfl)
@[simp] private theorem pc1325 :
    Artifact.submissionArtifact.instructionPC 1325 = 1830 :=
  pcStep pc1324 (by rfl)
@[simp] private theorem pc1326 :
    Artifact.submissionArtifact.instructionPC 1326 = 1831 :=
  pcStep pc1325 (by rfl)
@[simp] private theorem pc1327 :
    Artifact.submissionArtifact.instructionPC 1327 = 1833 :=
  pcStep pc1326 (by rfl)
@[simp] private theorem pc1328 :
    Artifact.submissionArtifact.instructionPC 1328 = 1834 :=
  pcStep pc1327 (by rfl)
@[simp] private theorem pc1329 :
    Artifact.submissionArtifact.instructionPC 1329 = 1835 :=
  pcStep pc1328 (by rfl)
@[simp] private theorem pc1330 :
    Artifact.submissionArtifact.instructionPC 1330 = 1836 :=
  pcStep pc1329 (by rfl)
@[simp] private theorem pc1331 :
    Artifact.submissionArtifact.instructionPC 1331 = 1839 :=
  pcStep pc1330 (by rfl)
@[simp] private theorem pc1332 :
    Artifact.submissionArtifact.instructionPC 1332 = 1840 :=
  pcStep pc1331 (by rfl)
@[simp] private theorem pc1333 :
    Artifact.submissionArtifact.instructionPC 1333 = 1842 :=
  pcStep pc1332 (by rfl)
@[simp] private theorem pc1334 :
    Artifact.submissionArtifact.instructionPC 1334 = 1843 :=
  pcStep pc1333 (by rfl)
@[simp] private theorem pc1335 :
    Artifact.submissionArtifact.instructionPC 1335 = 1844 :=
  pcStep pc1334 (by rfl)
@[simp] private theorem pc1336 :
    Artifact.submissionArtifact.instructionPC 1336 = 1846 :=
  pcStep pc1335 (by rfl)
@[simp] private theorem pc1337 :
    Artifact.submissionArtifact.instructionPC 1337 = 1847 :=
  pcStep pc1336 (by rfl)
@[simp] private theorem pc1338 :
    Artifact.submissionArtifact.instructionPC 1338 = 1849 :=
  pcStep pc1337 (by rfl)
@[simp] private theorem pc1339 :
    Artifact.submissionArtifact.instructionPC 1339 = 1850 :=
  pcStep pc1338 (by rfl)
@[simp] private theorem pc1340 :
    Artifact.submissionArtifact.instructionPC 1340 = 1851 :=
  pcStep pc1339 (by rfl)
@[simp] private theorem pc1341 :
    Artifact.submissionArtifact.instructionPC 1341 = 1852 :=
  pcStep pc1340 (by rfl)
@[simp] private theorem pc1342 :
    Artifact.submissionArtifact.instructionPC 1342 = 1853 :=
  pcStep pc1341 (by rfl)
@[simp] private theorem pc1343 :
    Artifact.submissionArtifact.instructionPC 1343 = 1854 :=
  pcStep pc1342 (by rfl)
@[simp] private theorem pc1344 :
    Artifact.submissionArtifact.instructionPC 1344 = 1855 :=
  pcStep pc1343 (by rfl)
@[simp] private theorem pc1345 :
    Artifact.submissionArtifact.instructionPC 1345 = 1856 :=
  pcStep pc1344 (by rfl)
@[simp] private theorem pc1346 :
    Artifact.submissionArtifact.instructionPC 1346 = 1857 :=
  pcStep pc1345 (by rfl)
@[simp] private theorem pc1347 :
    Artifact.submissionArtifact.instructionPC 1347 = 1858 :=
  pcStep pc1346 (by rfl)
@[simp] private theorem pc1348 :
    Artifact.submissionArtifact.instructionPC 1348 = 1859 :=
  pcStep pc1347 (by rfl)
@[simp] private theorem pc1349 :
    Artifact.submissionArtifact.instructionPC 1349 = 1860 :=
  pcStep pc1348 (by rfl)
@[simp] private theorem pc1350 :
    Artifact.submissionArtifact.instructionPC 1350 = 1861 :=
  pcStep pc1349 (by rfl)
@[simp] private theorem pc1351 :
    Artifact.submissionArtifact.instructionPC 1351 = 1862 :=
  pcStep pc1350 (by rfl)
@[simp] private theorem pc1352 :
    Artifact.submissionArtifact.instructionPC 1352 = 1863 :=
  pcStep pc1351 (by rfl)
@[simp] private theorem pc1353 :
    Artifact.submissionArtifact.instructionPC 1353 = 1864 :=
  pcStep pc1352 (by rfl)
@[simp] private theorem pc1354 :
    Artifact.submissionArtifact.instructionPC 1354 = 1865 :=
  pcStep pc1353 (by rfl)
@[simp] private theorem pc1355 :
    Artifact.submissionArtifact.instructionPC 1355 = 1866 :=
  pcStep pc1354 (by rfl)

/-! ## Jump destinations -/

private theorem jump1784 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1784 = true :=
  Artifact.isValidJumpDest_index 1286 (by rfl)

private theorem jump1810 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1810 = true :=
  Artifact.isValidJumpDest_index 1308 (by rfl)

private theorem jump1830 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1830 = true :=
  Artifact.isValidJumpDest_index 1325 (by rfl)

private theorem jump1859 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1859 = true :=
  Artifact.isValidJumpDest_index 1348 (by rfl)

/-! ## Word arithmetic the blocks need

`&&& 31` is the only bitwise operation the loader performs on `len`; it
reduces to `% 32` by the lemma `BigSerializeCorrect` already relies on. -/

theorem land_31_eq_mod (n : Nat) : n &&& 31 = n % 32 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod n 5

theorem land31_toNat (length : UInt256) :
    (UInt256.land length (UInt256.ofNat 31)).toNat = length.toNat % 32 := by
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : (31 : Nat) < 2 ^ 256)]
  exact land_31_eq_mod length.toNat

theorem loadEndAddr_toNat (dst length : UInt256) :
    (loadEndAddr dst length).toNat =
      (dst.toNat + 32 * fullLimbs length.toNat) % 2 ^ 256 := by
  have hlt : length.toNat % 32 ≤ length.toNat := Nat.mod_le _ _
  have hlen : length.toNat < 2 ^ 256 := length.val.isLt
  unfold loadEndAddr fullLimbs
  rw [Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_sub_cond, land31_toNat]
  rw [if_neg (by omega)]
  have hdiv := Nat.div_add_mod length.toNat 32
  have : length.toNat - length.toNat % 32 = 32 * (length.toNat / 32) := by omega
  rw [this]

theorem loadPtr_toNat (dst : UInt256) (k : Nat) :
    (loadPtr dst k).toNat = (dst.toNat + 32 * k) % 2 ^ 256 := by
  induction k with
  | zero =>
      have h : dst.toNat < 2 ^ 256 := dst.val.isLt
      show dst.toNat = (dst.toNat + 32 * 0) % 2 ^ 256
      rw [Nat.mul_zero, Nat.add_zero, Nat.mod_eq_of_lt h]
  | succ k ih =>
      have h32 : (UInt256.ofNat 32).toNat = 32 := by decide
      rw [loadPtr, Challenge.EvmProof.Word.word_toNat_add, h32, ih,
        Nat.add_mod_mod]
      congr 1
      ring

theorem loadRuns_le (dst length : UInt256) :
    loadRuns dst length ≤ fullLimbs length.toNat := by
  unfold loadRuns
  split <;> omega

theorem loadCount_le_length (dst length : UInt256) :
    loadCount dst length ≤ length.toNat := by
  have h := loadRuns_le dst length
  unfold loadCount fullLimbs at *
  split <;> omega

/-- Whenever the loop runs at all, the destination range does not wrap.  This
is the lemma that rules out a wrapped loop: a loop that is entered has an
unwrapped cursor for every index it visits. -/
theorem loadRuns_fit {dst length : UInt256} (h : 0 < loadRuns dst length) :
    dst.toNat + 32 * fullLimbs length.toNat < 2 ^ 256 := by
  by_contra hc
  rw [loadRuns, if_neg hc] at h
  omega

theorem loadRuns_eq_fullLimbs {dst length : UInt256}
    (h : 0 < loadRuns dst length) :
    loadRuns dst length = fullLimbs length.toNat := by
  rw [loadRuns, if_pos (loadRuns_fit h)]

/-! ### The one piece of 256-bit pointer arithmetic

`K - at` is exact in the ring even when `K` itself wraps, so the calldata
pointer for limb `k` is the honest byte offset `off + len - 32(k+1)`. -/

private theorem sub_mod_cancel {M S T : Nat} (hS : S < 2 * M)
    (hTS : T ≤ S) (hdiff : S - T < M) :
    (M + S % M - T) % M = S - T := by
  rcases Nat.lt_or_ge S M with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt, show M + S - T = M + (S - T) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt hdiff]
  · have hmod : S % M = S - M := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hmod, show M + (S - M) - T = S - T by omega, Nat.mod_eq_of_lt hdiff]

theorem loadBase_sub_ptr (offset length dst : UInt256) (k : Nat)
    (hoff : offset.toNat + length.toNat ≤ 2 ^ 256)
    (hfit : dst.toNat + 32 * fullLimbs length.toNat < 2 ^ 256)
    (hk : 32 * (k + 1) ≤ length.toNat) :
    (loadBase offset length dst - loadPtr dst k).toNat =
      offset.toNat + (length.toNat - 32 * (k + 1)) := by
  have hdst : dst.toNat < 2 ^ 256 := dst.val.isLt
  have hlen : length.toNat < 2 ^ 256 := length.val.isLt
  have hoffLt : offset.toNat < 2 ^ 256 := offset.val.isLt
  have hkfull : 32 * k < 32 * fullLimbs length.toNat := by
    unfold fullLimbs; omega
  have h32 : (UInt256.ofNat 32).toNat = 32 := by decide
  have hsub : (length - UInt256.ofNat 32).toNat = length.toNat - 32 := by
    rw [Challenge.EvmProof.Word.word_toNat_sub_cond, h32, if_neg (by omega)]
  have hadd : (offset + (length - UInt256.ofNat 32)).toNat =
      offset.toNat + (length.toNat - 32) := by
    rw [Challenge.EvmProof.Word.word_toNat_add, hsub,
      Nat.mod_eq_of_lt (by omega)]
  have hB : (loadBase offset length dst).toNat =
      (dst.toNat + (offset.toNat + (length.toNat - 32))) % 2 ^ 256 := by
    unfold loadBase
    rw [Challenge.EvmProof.Word.word_toNat_add, hadd]
  have hP : (loadPtr dst k).toNat = dst.toNat + 32 * k := by
    rw [loadPtr_toNat, Nat.mod_eq_of_lt (by omega)]
  rw [Challenge.EvmProof.Word.word_toNat_sub, hB, hP]
  rw [sub_mod_cancel (M := 2 ^ 256) (by omega) (by omega) (by omega)]
  omega

/-! ## Staged unfoldings

Each block certificate rewrites the *target* state with these before running
the block `simp`, so no `ite` ever has to be oriented inside the block
reduction. -/

theorem loadLimbValue_of_lt (calldata : ByteArray) (offset length dst : UInt256)
    (k : Nat) (hk : k < loadRuns dst length) :
    loadLimbValue calldata offset length dst k =
      loadWindow calldata offset length k := by
  rw [loadLimbValue, if_pos hk]

theorem loadLimbValue_of_ge (calldata : ByteArray) (offset length dst : UInt256)
    (k : Nat) (hk : ¬ k < loadRuns dst length) :
    loadLimbValue calldata offset length dst k =
      loadPartialValue calldata offset length := by
  rw [loadLimbValue, if_neg hk]

theorem loadMemory_succ (calldata : ByteArray) (offset length dst : UInt256)
    (k : Nat) (memory : ByteArray) (hk : k < loadCount dst length) :
    loadMemory calldata offset length dst (k + 1) memory =
      MachineState.writeBytes
        (loadMemory calldata offset length dst k memory)
        (Data.Bytes.natToBytesPadded
          (UInt256.lor
            (MachineState.readWord
              (loadMemory calldata offset length dst k memory)
              (loadPtr dst k).toNat)
            (loadLimbValue calldata offset length dst k)).toNat 32)
        (loadPtr dst k).toNat := by
  rw [loadMemory, if_pos hk]

theorem loadMemory_succ_of_ge (calldata : ByteArray)
    (offset length dst : UInt256) (k : Nat) (memory : ByteArray)
    (hk : ¬ k < loadCount dst length) :
    loadMemory calldata offset length dst (k + 1) memory =
      loadMemory calldata offset length dst k memory := by
  rw [loadMemory, if_neg hk]

theorem loadWords_succ (active dst length : UInt256) (k : Nat)
    (hk : k < loadCount dst length) :
    loadWords active dst length (k + 1) =
      UInt256.ofNat (MachineState.activeWordsAfter
        (UInt256.ofNat (MachineState.activeWordsAfter
          (loadWords active dst length k).toNat (loadPtr dst k).toNat 32)).toNat
        (loadPtr dst k).toNat 32) := by
  rw [loadWords, if_pos hk]

theorem loadWords_succ_of_ge (active dst length : UInt256) (k : Nat)
    (hk : ¬ k < loadCount dst length) :
    loadWords active dst length (k + 1) = loadWords active dst length k := by
  rw [loadWords, if_neg hk]

/-- Indices at or beyond `loadCount` change nothing. -/
theorem loadMemory_saturate (calldata : ByteArray) (offset length dst : UInt256)
    (memory : ByteArray) (j : Nat) (hj : loadCount dst length ≤ j) :
    loadMemory calldata offset length dst j memory =
      loadMemory calldata offset length dst (loadCount dst length) memory := by
  obtain ⟨d, rfl⟩ : ∃ d, j = loadCount dst length + d :=
    ⟨j - loadCount dst length, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show loadCount dst length + (d + 1) = (loadCount dst length + d) + 1 by
        omega, loadMemory_succ_of_ge _ _ _ _ _ _ (by omega), ih (by omega)]

theorem loadWords_saturate (active dst length : UInt256) (j : Nat)
    (hj : loadCount dst length ≤ j) :
    loadWords active dst length j =
      loadWords active dst length (loadCount dst length) := by
  obtain ⟨d, rfl⟩ : ∃ d, j = loadCount dst length + d :=
    ⟨j - loadCount dst length, by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show loadCount dst length + (d + 1) = (loadCount dst length + d) + 1 by
        omega, loadWords_succ_of_ge _ _ _ _ (by omega), ih (by omega)]

/-- `loadDone` and `loadReturned` are indexed by `len` for the benefit of the
callers; internally they sit at `loadCount`. -/
theorem loadDone_eq (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) :
    loadDone s offset length dst returnDest rest =
      { loadLoop s offset length dst (loadCount dst length) returnDest rest with
          pc := UInt256.ofNat 1859
          stack := loadFrame offset length dst returnDest
            (loadRuns dst length) rest } := by
  have h := loadCount_le_length dst length
  simp only [loadDone, loadLoop,
    loadMemory_saturate _ _ _ _ _ _ h, loadWords_saturate _ _ _ _ h]

theorem loadReturned_eq (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) :
    loadReturned s offset length dst returnDest rest =
      { loadLoop s offset length dst (loadCount dst length) returnDest rest with
          pc := returnDest, stack := rest } := by
  have h := loadCount_le_length dst length
  simp only [loadReturned, loadLoop,
    loadMemory_saturate _ _ _ _ _ _ h, loadWords_saturate _ _ _ _ h]

/-! ## Block certificates -/

set_option linter.unusedSimpArgs false in
/-- The stub: `JUMPDEST; PUSH2 1784; JUMP` moves the untouched caller frame
from the original entry PC 439 to the appended body at PC 1784. -/
theorem run_loadStub (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadStubPath
      (loadEntry s offset length dst returnDest rest) =
    some (loadBodyEntry s offset length dst returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have h1784 : (1784 : UInt256) = UInt256.ofNat 1784 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1784 : UInt256).toNat = true := by
    rw [show (1784 : UInt256).toNat = 1784 by decide]
    exact jump1784
  simp (disch := omega) [loadStubPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadEntry, loadBodyEntry, hcode, hrun, hvalid, jump1784,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1784]

/-! ### Setup

`loadRuns` decides the entry guard `at < end`: it is positive exactly when the
loop is entered.  The two lemmas below are the proof of that equivalence, and
between them they retire the wrapped case. -/

private theorem mod_lt_left {a b M : Nat} (ha : a < M) (hb : b < M)
    (hge : M ≤ a + b) : (a + b) % M < a := by
  have h1 : (a + b) % M = a + b - M := by
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  omega

theorem loadEnd_toNat_of_pos {dst length : UInt256}
    (h : 0 < loadRuns dst length) :
    (loadEndAddr dst length).toNat =
      dst.toNat + 32 * loadRuns dst length := by
  rw [loadEndAddr_toNat, Nat.mod_eq_of_lt (loadRuns_fit h),
    loadRuns_eq_fullLimbs h]

theorem lt_end_of_pos {dst length : UInt256} (h : 0 < loadRuns dst length) :
    UInt256.lt dst (loadEndAddr dst length) = UInt256.ofNat 1 := by
  have hend := loadEnd_toNat_of_pos h
  unfold UInt256.lt
  rw [if_pos (by omega)]

/-- The guard is false whenever `loadRuns = 0`, for *either* reason it can be
zero: `len < 32`, or a destination range that wraps.  In the wrapped case
`32 * (len/32) < 2^256` forces `end` strictly below `dst`. -/
theorem not_lt_end_of_zero {dst length : UInt256}
    (h : loadRuns dst length = 0) :
    UInt256.lt dst (loadEndAddr dst length) = UInt256.ofNat 0 := by
  have hdst : dst.toNat < 2 ^ 256 := dst.val.isLt
  have hlen : length.toNat < 2 ^ 256 := length.val.isLt
  have hfull : 32 * fullLimbs length.toNat < 2 ^ 256 := by
    unfold fullLimbs; omega
  have hend := loadEndAddr_toNat dst length
  have hnot : ¬ dst.toNat < (loadEndAddr dst length).toNat := by
    by_cases hfit : dst.toNat + 32 * fullLimbs length.toNat < 2 ^ 256
    · have hzero : fullLimbs length.toNat = 0 := by
        rw [loadRuns, if_pos hfit] at h; exact h
      rw [hend, Nat.mod_eq_of_lt hfit, hzero]
      omega
    · have := mod_lt_left (a := dst.toNat)
        (b := 32 * fullLimbs length.toNat) (M := 2 ^ 256) hdst hfull (by omega)
      omega
  unfold UInt256.lt
  rw [if_neg hnot]

set_option linter.unusedSimpArgs false in
/-- Setup, loop entered: build `end`, `K`, `at := dst`, guard true. -/
theorem run_loadSetup (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hruns : 0 < loadRuns dst length)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadSetupPath
      (loadBodyEntry s offset length dst returnDest rest) =
    some (loadLoop s offset length dst 0 returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  have hlt : UInt256.lt dst
      (dst + (length - UInt256.land length (UInt256.ofNat 31))) =
        UInt256.ofNat 1 := by
    simpa [loadEndAddr] using lt_end_of_pos hruns
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadSetupPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadBodyEntry, loadLoop, loadFrame, loadPtr, loadBase, loadEndAddr,
    loadMemory, loadWords, hrun, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h31, h32, hlt, honeIsZero]

set_option linter.unusedSimpArgs false in
/-- Setup, loop skipped: the guard `at < end` is false, so control goes
straight to the tail with no full limb written. -/
theorem run_loadSetupSkip (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hruns : loadRuns dst length = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadSetupPath
      (loadBodyEntry s offset length dst returnDest rest) =
    some (loadTailAt s offset length dst 0 returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h1830 : (1830 : UInt256) = UInt256.ofNat 1830 := by decide
  have hzeroIsZero : (UInt256.ofNat 0).isZero.toNat = 1 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1830 : UInt256).toNat = true := by
    rw [show (1830 : UInt256).toNat = 1830 by decide]
    exact jump1830
  have hlt : UInt256.lt dst
      (dst + (length - UInt256.land length (UInt256.ofNat 31))) =
        UInt256.ofNat 0 := by
    simpa [loadEndAddr] using not_lt_end_of_zero hruns
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadSetupPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadBodyEntry, loadTailAt, loadLoop, loadFrame, loadPtr, loadBase,
    loadEndAddr, loadMemory, loadWords, hcode, hrun, hvalid, jump1830,
    UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h31, h32, h1830, hlt, hzeroIsZero]

/-! ### The full-limb loop -/

theorem loadPtr_toNat_of_le {dst length : UInt256} {k : Nat}
    (hpos : 0 < loadRuns dst length) (hk : k ≤ loadRuns dst length) :
    (loadPtr dst k).toNat = dst.toNat + 32 * k := by
  have hfit := loadRuns_fit hpos
  have hN := loadRuns_eq_fullLimbs hpos
  rw [loadPtr_toNat, Nat.mod_eq_of_lt (by omega)]

set_option linter.unusedSimpArgs false in
/-- One full limb, guard true: `mstore(at, mload(at) ||| calldataload(K - at))`
then `at += 32` and back to the loop head. -/
theorem run_loadLoop (s : State) (offset length dst returnDest : UInt256)
    (k : Nat) (rest : List UInt256) (hcap : rest.length < 1015)
    (hoff : offset.toNat + length.toNat ≤ 2 ^ 256)
    (hk : k + 1 < loadRuns dst length)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadLoopPath
      (loadLoop s offset length dst k returnDest rest) =
    some (loadLoop s offset length dst (k + 1) returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have hpos : 0 < loadRuns dst length := by omega
  have hcount : loadRuns dst length ≤ loadCount dst length := by
    unfold loadCount; split <;> omega
  have hguard : k < loadCount dst length := by omega
  have hlimb : k < loadRuns dst length := by omega
  have hfit := loadRuns_fit hpos
  have hN := loadRuns_eq_fullLimbs hpos
  have hend := loadEnd_toNat_of_pos hpos
  have hptrk : (loadPtr dst k).toNat = dst.toNat + 32 * k :=
    loadPtr_toNat_of_le hpos (by omega)
  have hcond : 32 + (loadPtr dst k).toNat < (loadEndAddr dst length).toNat := by
    rw [hptrk, hend]; omega
  have haddr : (loadBase offset length dst - loadPtr dst k).toNat =
      offset.toNat + (length.toNat - 32 * (k + 1)) :=
    loadBase_sub_ptr offset length dst k hoff (by omega)
      (by unfold fullLimbs at hN; omega)
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have h1810 : (1810 : UInt256) = UInt256.ofNat 1810 := by decide
  have honeIsZero : ¬ (UInt256.ofNat 1).toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1810 : UInt256).toNat = true := by
    rw [show (1810 : UInt256).toNat = 1810 by decide]
    exact jump1810
  rw [show loadLoop s offset length dst (k + 1) returnDest rest =
      { s with pc := UInt256.ofNat 1810
               stack := loadFrame offset length dst returnDest (k + 1) rest
               memory := MachineState.writeBytes
                 (loadMemory s.executionEnv.calldata offset length dst k s.memory)
                 (Data.Bytes.natToBytesPadded
                   (UInt256.lor
                     (MachineState.readWord
                       (loadMemory s.executionEnv.calldata offset length dst k
                         s.memory)
                       (loadPtr dst k).toNat)
                     (loadWindow s.executionEnv.calldata offset length k)).toNat
                   32)
                 (loadPtr dst k).toNat
               activeWords := UInt256.ofNat (MachineState.activeWordsAfter
                 (UInt256.ofNat (MachineState.activeWordsAfter
                   (loadWords s.activeWords dst length k).toNat
                   (loadPtr dst k).toNat 32)).toNat
                 (loadPtr dst k).toNat 32) } by
    simp only [loadLoop, loadMemory_succ _ _ _ _ _ _ hguard,
      loadWords_succ _ _ _ _ hguard, loadLimbValue_of_lt _ _ _ _ _ hlimb]]
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadLoopPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadLoop, loadFrame, loadPtr, loadWindow, haddr, hcode, hrun, hvalid,
    jump1810, State.activeWordsAfterUInt256, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h32, h1810, hcond, honeIsZero]

set_option linter.unusedSimpArgs false in
/-- The last full limb: the closing guard fails and control falls through to
the tail at PC 1830. -/
theorem run_loadLoopLast (s : State) (offset length dst returnDest : UInt256)
    (k : Nat) (rest : List UInt256) (hcap : rest.length < 1015)
    (hoff : offset.toNat + length.toNat ≤ 2 ^ 256)
    (hk : k + 1 = loadRuns dst length)
    (_hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadLoopPath
      (loadLoop s offset length dst k returnDest rest) =
    some (loadTailAt s offset length dst (k + 1) returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have hpos : 0 < loadRuns dst length := by omega
  have hcount : loadRuns dst length ≤ loadCount dst length := by
    unfold loadCount; split <;> omega
  have hguard : k < loadCount dst length := by omega
  have hlimb : k < loadRuns dst length := by omega
  have hfit := loadRuns_fit hpos
  have hN := loadRuns_eq_fullLimbs hpos
  have hend := loadEnd_toNat_of_pos hpos
  have hptrk : (loadPtr dst k).toNat = dst.toNat + 32 * k :=
    loadPtr_toNat_of_le hpos (by omega)
  have hcond : ¬ (32 + (loadPtr dst k).toNat <
      (loadEndAddr dst length).toNat) := by
    rw [hptrk, hend]; omega
  have haddr : (loadBase offset length dst - loadPtr dst k).toNat =
      offset.toNat + (length.toNat - 32 * (k + 1)) :=
    loadBase_sub_ptr offset length dst k hoff (by omega)
      (by unfold fullLimbs at hN; omega)
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have hzeroIsZero : (UInt256.ofNat 0).toNat = 0 := by decide
  rw [show loadTailAt s offset length dst (k + 1) returnDest rest =
      { s with pc := UInt256.ofNat 1830
               stack := loadFrame offset length dst returnDest (k + 1) rest
               memory := MachineState.writeBytes
                 (loadMemory s.executionEnv.calldata offset length dst k s.memory)
                 (Data.Bytes.natToBytesPadded
                   (UInt256.lor
                     (MachineState.readWord
                       (loadMemory s.executionEnv.calldata offset length dst k
                         s.memory)
                       (loadPtr dst k).toNat)
                     (loadWindow s.executionEnv.calldata offset length k)).toNat
                   32)
                 (loadPtr dst k).toNat
               activeWords := UInt256.ofNat (MachineState.activeWordsAfter
                 (UInt256.ofNat (MachineState.activeWordsAfter
                   (loadWords s.activeWords dst length k).toNat
                   (loadPtr dst k).toNat 32)).toNat
                 (loadPtr dst k).toNat 32) } by
    simp only [loadTailAt, loadLoop, loadMemory_succ _ _ _ _ _ _ hguard,
      loadWords_succ _ _ _ _ hguard, loadLimbValue_of_lt _ _ _ _ _ hlimb]]
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadLoopPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadLoop, loadFrame, loadPtr, loadWindow, haddr, hrun,
    State.activeWordsAfterUInt256, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h32, hcond, hzeroIsZero]

/-! ### Tail, partial limb and exit -/

theorem loadCount_of_mod_zero {dst length : UInt256}
    (hr : length.toNat % 32 = 0) :
    loadCount dst length = loadRuns dst length := by
  rw [loadCount, if_pos hr, Nat.add_zero]

theorem loadCount_of_mod_ne {dst length : UInt256}
    (hr : ¬ length.toNat % 32 = 0) :
    loadCount dst length = loadRuns dst length + 1 := by
  rw [loadCount, if_neg hr]

set_option linter.unusedSimpArgs false in
/-- Tail with `len % 32 = 0`: nothing more to write, jump to the exit. -/
theorem run_loadTailDone (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hr : length.toNat % 32 = 0)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadTailPath
      (loadTailAt s offset length dst (loadRuns dst length) returnDest rest) =
    some (loadDone s offset length dst returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have hcountEq : loadCount dst length = loadRuns dst length :=
    loadCount_of_mod_zero hr
  have hland : length.toNat &&& 31 = 0 := by rw [land_31_eq_mod]; exact hr
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h1859 : (1859 : UInt256) = UInt256.ofNat 1859 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1859 : UInt256).toNat = true := by
    rw [show (1859 : UInt256).toNat = 1859 by decide]
    exact jump1859
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadTailPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadTailAt, loadDone_eq, hcountEq, loadLoop, loadFrame, hcode, hrun,
    hvalid, jump1859, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h31, h1859, hland]

set_option linter.unusedSimpArgs false in
/-- Tail with `len % 32 ≠ 0`: fall through to the partial-limb block. -/
theorem run_loadTail (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hr : ¬ length.toNat % 32 = 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadTailPath
      (loadTailAt s offset length dst (loadRuns dst length) returnDest rest) =
    some (loadPartialEntry s offset length dst returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have hland : length.toNat &&& 31 = length.toNat % 32 := land_31_eq_mod _
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadTailPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadTailAt, loadPartialEntry, loadLoop, loadFrame, hrun, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h31, hland, hr]

set_option linter.unusedSimpArgs false in
/-- The single partial top limb:
`mstore(at, mload(at) ||| (calldataload(off) >> (8 * (32 - r))))`. -/
theorem run_loadPartial (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hr : ¬ length.toNat % 32 = 0)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadPartialPath
      (loadPartialEntry s offset length dst returnDest rest) =
    some (loadDone s offset length dst returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  have hcountEq : loadCount dst length = loadRuns dst length + 1 :=
    loadCount_of_mod_ne hr
  have hguard : loadRuns dst length < loadCount dst length := by omega
  have hge : ¬ loadRuns dst length < loadRuns dst length := by omega
  have h3 : (3 : UInt256) = UInt256.ofNat 3 := by decide
  have h31 : (31 : UInt256) = UInt256.ofNat 31 := by decide
  have h32 : (32 : UInt256) = UInt256.ofNat 32 := by decide
  have hlandWord : UInt256.land length (UInt256.ofNat 31) =
      UInt256.ofNat (length.toNat % 32) := by
    apply Challenge.EvmProof.Word.word_ext
    rw [land31_toNat, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : length.toNat % 32 < 2 ^ 256)]
  have hshift : UInt256.shiftLeft
      (UInt256.ofNat 32 - UInt256.land length (UInt256.ofNat 31))
      (UInt256.ofNat 3) =
        UInt256.ofNat ((32 - length.toNat % 32) * 8) := by
    rw [hlandWord,
      Challenge.EvmProof.Word.ofNat_sub_ofNat (by omega) (by norm_num),
      Challenge.EvmProof.Word.shiftLeft_ofNat (by omega) (by omega)
        (by simp only [show (2 : Nat) ^ 3 = 8 by norm_num]; omega),
      show (2 : Nat) ^ 3 = 8 by norm_num]
  rw [show loadDone s offset length dst returnDest rest =
      { s with pc := UInt256.ofNat 1859
               stack := loadFrame offset length dst returnDest
                 (loadRuns dst length) rest
               memory := MachineState.writeBytes
                 (loadMemory s.executionEnv.calldata offset length dst
                   (loadRuns dst length) s.memory)
                 (Data.Bytes.natToBytesPadded
                   (UInt256.lor
                     (MachineState.readWord
                       (loadMemory s.executionEnv.calldata offset length dst
                         (loadRuns dst length) s.memory)
                       (loadPtr dst (loadRuns dst length)).toNat)
                     (loadPartialValue s.executionEnv.calldata offset
                       length)).toNat 32)
                 (loadPtr dst (loadRuns dst length)).toNat
               activeWords := UInt256.ofNat (MachineState.activeWordsAfter
                 (UInt256.ofNat (MachineState.activeWordsAfter
                   (loadWords s.activeWords dst length
                     (loadRuns dst length)).toNat
                   (loadPtr dst (loadRuns dst length)).toNat 32)).toNat
                 (loadPtr dst (loadRuns dst length)).toNat 32) } by
    rw [loadDone_eq, hcountEq]
    simp only [loadLoop, loadMemory_succ _ _ _ _ _ _ hguard,
      loadWords_succ _ _ _ _ hguard, loadLimbValue_of_ge _ _ _ _ _ hge]]
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadPartialPath,
    opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadPartialEntry, loadLoop, loadFrame, loadPartialValue, hshift, hrun,
    State.activeWordsAfterUInt256, List.exchange,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h3, h31, h32]

set_option linter.unusedSimpArgs false in
/-- Drop the seven-slot frame and jump to the return address. -/
theorem run_loadExit (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadExitPath
      (loadDone s offset length dst returnDest rest) =
    some (loadReturned s offset length dst returnDest rest) := by
  have hc : ∀ n ≤ 9, rest.length + n < 1024 := by omega
  simp (config := { maxSteps := 1200000 }) (disch := omega) [loadExitPath,
    opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loadDone_eq, loadReturned_eq, loadLoop, loadFrame, hcode, hrun, hvalid,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc]

/-! ## Gas-parametric composition -/

/-- The full-limb loop, from the body entry to the tail head.  `loadRuns` is
matched on as a `Nat` because `GasSteps` lives in `Type`.

Note there is no iteration index beyond `loadRuns` for which a certificate
exists: `run_loadLoop` demands `k + 1 < loadRuns` and `run_loadLoopLast`
demands `k + 1 = loadRuns`.  The composition below is therefore exactly
`loadRuns` iterations and a wrapped loop cannot re-enter. -/
def gasSteps_loadFullLimbs (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hoff : offset.toNat + length.toNat ≤ 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (N : Nat) (hN : loadRuns dst length = N) :
    Challenge.EvmProof.GasSteps
      (loadBodyEntry s offset length dst returnDest rest)
      (loadTailAt s offset length dst N returnDest rest) := by
  cases N with
  | zero =>
      exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka loadSetupPath
          (by simpa [loadBodyEntry, Artifact.submissionArtifact] using hcode)
          (by simpa [loadBodyEntry, State.fork] using hfork)
          (run_loadSetupSkip s offset length dst returnDest rest hcap hN hcode
            hrun)
          (by simpa [loadBodyEntry] using hrun)
          (by simpa [loadBodyEntry, State.fork] using hnp)
  | succ M =>
      have hsetup := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka loadSetupPath
          (by simpa [loadBodyEntry, Artifact.submissionArtifact] using hcode)
          (by simpa [loadBodyEntry, State.fork] using hfork)
          (run_loadSetup s offset length dst returnDest rest hcap (by omega)
            hrun)
          (by simpa [loadBodyEntry] using hrun)
          (by simpa [loadBodyEntry, State.fork] using hnp)
      have hbody := Challenge.EvmProof.GasSteps.iterateBounded
        (I := fun i => loadLoop s offset length dst i returnDest rest) M
        (fun i hi => Challenge.EvmProof.Stepper.runLocatedBlock_sound
          Artifact.submissionArtifact .Osaka loadLoopPath
            (by simpa [loadLoop, Artifact.submissionArtifact] using hcode)
            (by simpa [loadLoop, State.fork] using hfork)
            (run_loadLoop s offset length dst returnDest i rest hcap hoff
              (by omega) hcode hrun)
            (by simpa [loadLoop] using hrun)
            (by simpa [loadLoop, State.fork] using hnp))
      have hlast := Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka loadLoopPath
          (by simpa [loadLoop, Artifact.submissionArtifact] using hcode)
          (by simpa [loadLoop, State.fork] using hfork)
          (run_loadLoopLast s offset length dst returnDest M rest hcap hoff
            (by omega) hcode hrun)
          (by simpa [loadLoop] using hrun)
          (by simpa [loadLoop, State.fork] using hnp)
      exact hsetup.trans (hbody.trans hlast)

/-- Tail head to exit head: the single partial limb, when there is one. -/
def gasSteps_loadTailToDone (s : State) (offset length dst returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1015)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (loadTailAt s offset length dst (loadRuns dst length) returnDest rest)
      (loadDone s offset length dst returnDest rest) := by
  if hr : length.toNat % 32 = 0 then
    exact Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka loadTailPath
        (by simpa [loadTailAt, loadLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [loadTailAt, loadLoop, State.fork] using hfork)
        (run_loadTailDone s offset length dst returnDest rest hcap hr hcode
          hrun)
        (by simpa [loadTailAt, loadLoop] using hrun)
        (by simpa [loadTailAt, loadLoop, State.fork] using hnp)
  else
    exact (Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka loadTailPath
        (by simpa [loadTailAt, loadLoop, Artifact.submissionArtifact] using hcode)
        (by simpa [loadTailAt, loadLoop, State.fork] using hfork)
        (run_loadTail s offset length dst returnDest rest hcap hr hrun)
        (by simpa [loadTailAt, loadLoop] using hrun)
        (by simpa [loadTailAt, loadLoop, State.fork] using hnp)).trans
      (Challenge.EvmProof.Stepper.runLocatedBlock_sound
        Artifact.submissionArtifact .Osaka loadPartialPath
          (by simpa [loadPartialEntry, loadLoop,
            Artifact.submissionArtifact] using hcode)
          (by simpa [loadPartialEntry, loadLoop, State.fork] using hfork)
          (run_loadPartial s offset length dst returnDest rest hcap hr hrun)
          (by simpa [loadPartialEntry, loadLoop] using hrun)
          (by simpa [loadPartialEntry, loadLoop, State.fork] using hnp))

/-- The whole certified `loadBigEndian` call, from the caller's frame at the
original entry PC 439 back to the caller.  Signature unchanged from the
byte-at-a-time version, so `BigSetup` and `BigBase` call sites are untouched. -/
def gasSteps_loadBigEndian (s : State) (offset length : Nat)
    (dst returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hoffsetWord : offset < 2 ^ 256)
    (hoffset : offset + length ≤ 2 ^ 256)
    (hlength : length < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (loadEntry s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest)
      (loadReturned s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest) := by
  have hcap' : rest.length < 1015 := by omega
  have hoff : (UInt256.ofNat offset).toNat + (UInt256.ofNat length).toNat ≤
      2 ^ 256 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hoffsetWord, Nat.mod_eq_of_lt hlength]
    exact hoffset
  have hstub := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadStubPath
      (by simpa [loadEntry, Artifact.submissionArtifact] using hcode)
      (by simpa [loadEntry, State.fork] using hfork)
      (run_loadStub s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest hcap' hcode hrun)
      (by simpa [loadEntry] using hrun)
      (by simpa [loadEntry, State.fork] using hnp)
  have hloop := gasSteps_loadFullLimbs s (UInt256.ofNat offset)
    (UInt256.ofNat length) dst returnDest rest hcap' hoff hcode hfork hrun hnp
    (loadRuns dst (UInt256.ofNat length)) rfl
  have htail := gasSteps_loadTailToDone s (UInt256.ofNat offset)
    (UInt256.ofNat length) dst returnDest rest hcap' hcode hfork hrun hnp
  have hexit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadExitPath
      (by simpa [loadDone, loadLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [loadDone, loadLoop, State.fork] using hfork)
      (run_loadExit s (UInt256.ofNat offset) (UInt256.ofNat length) dst
        returnDest rest hcap' hcode hrun hvalid)
      (by simpa [loadDone, loadLoop] using hrun)
      (by simpa [loadDone, loadLoop, State.fork] using hnp)
  exact hstub.trans (hloop.trans (htail.trans hexit))

end Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad
