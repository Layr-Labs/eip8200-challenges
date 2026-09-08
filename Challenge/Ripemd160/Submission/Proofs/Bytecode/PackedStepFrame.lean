import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-!
# The one-step execution frame for the packed gate

Every constant here was read out of the emitted program at
`/tmp/packed-gate.hex` (decoded sha256 `ed34b6a2…`, 5,358 bytes, 4,572
instructions), by decoding and running it, not reconstructed from what the
arithmetic wanted.  It was then cross-checked against the layout map, and the
map and the decode agree on every index and program counter.

## The frame, top-first

At the compression entry (index 296, PC 538) the stack is `[ptr, ret, Xoff,
Xend]`.  By the first round (index 498, PC 886) it is **nineteen deep**:

    [A, B, C, D, E,  MLR, ML, MR, c,  s17,s18,s19,s20,s21,s22,  K,  ret, Xoff, Xend]
     └── five rotating registers ──┘  └────── fourteen-deep invariant suffix ──────┘

Only the first five slots move.  The suffix is the four masks-and-multiplier,
six resident shift amounts, the packed round constant, and the three caller
slots.

## Two facts about the real program that the shape has to respect

**Instruction count is not the step invariant.**  Measured over all 79
transitions, the body length is set by the ROUND GROUP, not by parity and not
uniformly: 47 for rounds 0–15, 53 for 16–31, 43 for 32–47, 53 for 48–63, 47 for
64–79, each with `+3` at the four sixteen-boundaries where the constant is
swapped before the label.  Six distinct lengths occur: 43, 46, 47, 50, 53, 56.
That tracks the three shapes of the packed `f` — the blend form at `r = 0, 4`,
the select form at `r = 1, 3`, and the short form at `r = 2`.  A trace
interface phrased as "one step is `N` instructions" is false.

**The physical register order alternates with period two.**  This is the
correction that matters most, and it was found by running the artifact rather
than by reading it.  The logical round produces `(A,B,C,D,E) := (E, T, B,
rol10 C, D)`, but the emitted code does not reorder the stack to match: it
brings the new `A` to the top and leaves the rest where they fall.  Measured
across rounds 0–7, the physical order entering a round is

    round 0, 2, 4, 6 …   [A, B, C, D, E]      (identity)
    round 1, 3, 5, 7 …   [A, C, B, E, D]      (B↔C and D↔E transposed)

and it alternates exactly, with the fourteen-slot suffix stable throughout.  A
frame that fixes `[A,B,C,D,E]` at every round — which is what an earlier draft
of this file did — is correct at round 0 and WRONG at every odd round.  The
`Phase` below carries it.

**The round constant is replaced before the label, not inside the round.**
That is the source of the 47/50 difference, and it is why `replaceK` is a
separate operation below rather than a field update folded into `stepFrame`.
Do not assume a uniform round across the multiples of sixteen.

## Measured memory map of the compression

Read by executing the artifact on one 64-byte block and recording every
`MSTORE` / `MLOAD` target:

    spread word slots   bytes [0, 272)      stores at 0x00,0x10,…,0xf0
    swap scratch        bytes [288, 352)    0x120, 0x140
    H registers         bytes [352, 480]    0x160,0x180,0x1a0,0x1c0,0x1e0
    message block       from 512            entry `ptr` = 0x200

The compression stores nothing above 512; its largest `MSTORE` target is
`0x1e0`.  Two of the three relayed recut offsets agree with this — `H` at
352..480 and message at ≥512 — but "word storage above 512" does NOT: the
spread word storage is at `[0, 272)`.  Recorded rather than reconciled.

## Two hazards this file was caught by, both worth carrying

**Record-update syntax silently keeps fields you forget.**  `tracesStep_regs`
was written as `{ f with regs := … }` before `Frame` gained its `phase` field.
When the field was added, `{ f with … }` kept the OLD phase while `stepFrame`
flipped it, so the restatement quietly asserted that a round leaves the frame in
the same phase — contradicting the alternation measured from the artifact.  The
elaborator caught it as a type mismatch.  Anywhere a structure gains a field,
every `{x with …}` that should update it compiles unchanged and means something
different.

**`unsolved goals` injects `sorryAx`.**  A proof that leaves a goal open does not
merely fail — the declaration is admitted with `sorryAx`, and everything
downstream inherits it.  So a source file with no occurrence of the placeholder
token can still be unsound, and only `#print axioms` after a completed
elaboration settles it.  The proofs below therefore avoid `rw` steps that may or
may not close their goal, in favour of destructuring the frame and letting both
sides reduce.

## Reach

`K` sits at depth 16 counted from the top, exactly at `DUP16`/`SWAP16` reach,
with `ret`, `Xoff`, `Xend` beyond it.  Anything that has to touch `K` is at the
edge of the instruction set, so the suffix cannot grow without the round body
losing access to its own constant.

STATUS: WRITTEN, NOT ELABORATED.  No admitted goals; the file contains zero
occurrences of the placeholder token, so a grep and this claim agree.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepCorrected
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedCompression

/-- The fourteen slots below the rotating registers.  They are carried
unchanged through a round; only `konst` is ever rewritten, and only between
rounds. -/
structure Suffix where
  maskLRv : UInt256
  maskLv : UInt256
  maskRv : UInt256
  cMulv : UInt256
  s17 : UInt256
  s18 : UInt256
  s19 : UInt256
  s20 : UInt256
  s21 : UInt256
  s22 : UInt256
  konst : UInt256
  ret : UInt256
  xoff : UInt256
  xend : UInt256

/-- Which of the two physical register orders the frame is in.  The emitted
code alternates every round. -/
inductive Phase where
  | even
  | odd
deriving DecidableEq

def Phase.flip : Phase → Phase
  | .even => .odd
  | .odd => .even

/-- The whole nineteen-slot round frame. -/
structure Frame where
  regs : Regs
  suf : Suffix
  phase : Phase

/-- The suffix as it sits on the machine stack, top-first. -/
def suffixStack (s : Suffix) : List UInt256 :=
  [s.maskLRv, s.maskLv, s.maskRv, s.cMulv,
   s.s17, s.s18, s.s19, s.s20, s.s21, s.s22,
   s.konst, s.ret, s.xoff, s.xend]

/-- The five register slots as they physically sit, which depends on the
phase. -/
def regsStack : Phase → Regs → List UInt256
  | .even, g => [g.a, g.b, g.c, g.d, g.e]
  | .odd, g => [g.a, g.c, g.b, g.e, g.d]

/-- The frame as it sits on the machine stack, top-first. -/
def frameStack (f : Frame) : List UInt256 :=
  regsStack f.phase f.regs ++ suffixStack f.suf

/-- One round: the registers rotate, the suffix does not move. -/
def stepFrame (r sl sr : Nat) (X : UInt256) (f : Frame) : Frame :=
  { f with regs := correctedStep r sl sr f.regs X f.suf.konst
           phase := f.phase.flip }

/-- The between-rounds constant swap at each multiple of sixteen.  Emitted
BEFORE the round label, which is why rounds 15 and 16 differ in length. -/
def replaceK (k : UInt256) (f : Frame) : Frame :=
  { f with suf := { f.suf with konst := k } }

/-! ## Frame algebra -/

theorem suffixStack_length (s : Suffix) : (suffixStack s).length = 14 := rfl

theorem regsStack_length (ph : Phase) (g : Regs) :
    (regsStack ph g).length = 5 := by
  cases ph <;> rfl

theorem frameStack_length (f : Frame) : (frameStack f).length = 19 := by
  obtain ⟨regs, suf, phase⟩ := f
  cases phase <;> rfl

/-- A round flips the phase; two rounds restore it. -/
theorem stepFrame_phase (r sl sr : Nat) (X : UInt256) (f : Frame) :
    (stepFrame r sl sr X f).phase = f.phase.flip := rfl

theorem Phase.flip_flip (ph : Phase) : ph.flip.flip = ph := by
  cases ph <;> rfl

/-- The round touches only the top five slots. -/
theorem stepFrame_suffix (r sl sr : Nat) (X : UInt256) (f : Frame) :
    (stepFrame r sl sr X f).suf = f.suf := rfl

theorem stepFrame_drop (r sl sr : Nat) (X : UInt256) (f : Frame) :
    (frameStack (stepFrame r sl sr X f)).drop 5 = (frameStack f).drop 5 := by
  obtain ⟨regs, suf, phase⟩ := f
  cases phase <;> rfl

/-- The round's effect on the register slots IS `correctedStep`. -/
theorem stepFrame_regs (r sl sr : Nat) (X : UInt256) (f : Frame) :
    (stepFrame r sl sr X f).regs = correctedStep r sl sr f.regs X f.suf.konst :=
  rfl

/-- The constant swap moves nothing but the constant. -/
theorem replaceK_regs (k : UInt256) (f : Frame) : (replaceK k f).regs = f.regs :=
  rfl

theorem replaceK_drop (k : UInt256) (f : Frame) :
    (frameStack (replaceK k f)).take 5 = (frameStack f).take 5 := by
  obtain ⟨regs, suf, phase⟩ := f
  cases phase <;> rfl

/-! ## Where the round's message word comes from

Swept over all eighty rounds of the artifact, not sampled: the round begins
`PUSH lo ; MLOAD ; PUSH hi ; MLOAD ; OR`, and that five-instruction pattern
occurs exactly eighty times in the compression region.  The immediates are

    lo = 16 * r[i]           80/80
    hi = 16 * rP[i] + 8      80/80   (without the `+ 8`, 80/80 FAIL)

The `+ 8` is the mechanism, not an adjustment.  `MLOAD` reads a 32-byte
big-endian window, so a field at bytes `[b, b+4)` appears at bits 0..31 of a
load at `b - 28`, and at bits 64..95 of a load at `b - 20`.  The two offsets
differ by 8 bytes = 64 bits, which is exactly the lane-1 displacement.  The two
lanes are landed by moving the read window, never by a shift instruction. -/

def leftOffset (i : Nat) : Nat := 16 * Crypto.Ripemd160.r[i]!

def rightOffset (i : Nat) : Nat := 16 * Crypto.Ripemd160.rP[i]! + 8

/-- The left load lands its field at bits 0..31. -/
theorem leftOffset_lane0 (i : Nat) :
    leftOffset i + 28 = 16 * Crypto.Ripemd160.r[i]! + 28 := rfl

/-- The right load lands its field at bits 64..95 — eight bytes lower in the
window is sixty-four bits higher in the value. -/
theorem rightOffset_lane1 (i : Nat) :
    rightOffset i + 20 = 16 * Crypto.Ripemd160.rP[i]! + 28 := by
  unfold rightOffset
  omega

/-! ## `GapZero`, and why it is not bookkeeping

The spread writes 32 bytes at `16*k` for `k = 15 … 0`, covering `[0, 272)`.
The swap scratch begins at 288.  The right-lane load for message index 15 sits
at `16*15 + 8 = 248` and reads `[248, 280)`, so bytes **`[272, 280)` are read
and never written**.

Those eight bytes land in the LOW 64 bits of that load, so they corrupt
**lane 0**, and they do so on exactly the five rounds with `rP[i] = 15` —
rounds 10, 25, 32, 54, 65 — confirmed at five emitted sites in this artifact.
A step correspondence stated without `GapZero` is therefore FALSE at five known
indices, and it would still elaborate, because nothing in an arbitrary machine
state forces those bytes to be zero.  That is the same shape as a vacuous
premise, except the missing one is load-bearing. -/

/-- The eight bytes the spread never writes and the right-lane load reads.
Stated on an abstract byte accessor so this file does not depend on the machine
state type. -/
def GapZero (byteAt : Nat → Nat) : Prop :=
  ∀ i, 272 ≤ i → i < 280 → byteAt i = 0

/-- The rounds at which the gap is actually read. -/
def gapReadRounds : List Nat := [10, 25, 32, 54, 65]

theorem gap_read_extent (i : Nat) (h : Crypto.Ripemd160.rP[i]! = 15) :
    rightOffset i = 248 ∧ rightOffset i + 32 = 280 := by
  unfold rightOffset
  rw [h]
  omega

/-- What the machine must establish about the round's message word.  `GapZero`
is a conjunct, not a side remark: without it this is false at
`gapReadRounds`. -/
def StepLoad (byteAt : Nat → Nat) (loadAt : Nat → UInt256)
    (i : Nat) (X : UInt256) : Prop :=
  GapZero byteAt ∧
    X = UInt256.lor (loadAt (leftOffset i)) (loadAt (rightOffset i))

/-! ## The trace interface

`TracesStep` is the obligation a machine-level proof must supply for one round:
starting from a state whose stack is this frame, the emitted block leaves a
state whose stack is the stepped frame.  It is stated over an abstract
"stack of a state" accessor so that this file does not depend on the artifact
instruction table, which does not yet exist for this candidate.

Discharging it needs the `Located` path for the round's instruction range,
which needs the regenerated table.  That is named, not assumed. -/

/-- One machine round, as a relation on stacks.  This is the STACK half only;
the memory half is `StepLoad`, and a machine-level proof owes both.  Keeping
them separate is deliberate — it is what stops `GapZero` from being quietly
dropped when only the stack shape is checked. -/
def TracesStep (run : List UInt256 → Option (List UInt256))
    (r sl sr : Nat) (X : UInt256) (f : Frame) : Prop :=
  run (frameStack f) = some (frameStack (stepFrame r sl sr X f))

/-- If the machine traces the round, then the register quintuple it leaves is
exactly the one the arithmetic layer proved about.  This is the join between
the execution side and `correctedStep_represents_final`. -/
theorem tracesStep_regs
    (run : List UInt256 → Option (List UInt256))
    (r sl sr : Nat) (X : UInt256) (f : Frame)
    (h : TracesStep run r sl sr X f) :
    run (frameStack f)
      = some (frameStack
          { regs := correctedStep r sl sr f.regs X f.suf.konst
            suf := f.suf
            phase := f.phase.flip }) := h

/-- Folding the interface over a round range: the suffix is invariant across
any number of rounds, whatever the per-round parameters are.  This is the
statement that makes an eighty-round trace induction possible without assuming
uniform rounds. -/
def framesAgree (f g : Frame) : Prop := f.suf = g.suf

theorem stepFrame_framesAgree (r sl sr : Nat) (X : UInt256) (f : Frame) :
    framesAgree f (stepFrame r sl sr X f) := rfl

theorem framesAgree_trans {f g h : Frame}
    (hfg : framesAgree f g) (hgh : framesAgree g h) : framesAgree f h :=
  hfg.trans hgh

#print axioms regsStack_length
#print axioms stepFrame_phase
#print axioms leftOffset_lane0
#print axioms rightOffset_lane1
#print axioms gap_read_extent
#print axioms frameStack_length
#print axioms stepFrame_drop
#print axioms stepFrame_regs
#print axioms tracesStep_regs
#print axioms stepFrame_framesAgree

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
