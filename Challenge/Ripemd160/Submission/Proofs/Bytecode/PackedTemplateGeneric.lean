import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplatesRest

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Scaling ten templates to eighty rounds

A literal-index template is specific to one round, because `emitRound i` bakes
in that round's two offsets and two rotation amounts.  This module supplies the
three facts that let a template be stated over those four numbers instead, so
one lemma per (phase, group) covers all eight rounds of its class.

## Why this is not just the literal form with variables

Under a symbolic index nothing reduces: `pushOffset lo` and `shiftSupply vl`
are `if`-expressions on symbolic data, so `rfl` gets no traction, and the
literal-index templates' whole proof method disappears.  The replacement is to
prove each of those two constructs has a single *effect* regardless of which
branch it takes, and then to split the operation list at the four sites where
they occur.  `runOps_append` does the splitting; the two effect lemmas collapse
the branches.

* `pushOffset_effect` — both branches push `UInt256.ofNat v`.  The `PUSH0`
  branch pushes `0`, and `UInt256.ofNat 0` is `0`, so the artifact's use of the
  cheaper opcode at the five zero-offset rounds is invisible to the semantics
  even though it is visible in the bytes.
* `shiftSupply_effect` — the `push` branch pushes `UInt256.ofNat v` directly;
  the `dup` branch duplicates the stack slot at `v - 7`, which holds the same
  value when the resident constants are in place.  Note `(v - 6) - 1 = v - 7`:
  `DUP n` reads index `n - 1`, and the emitted index is `v - 6`.

## `SuffixStd` is falsifiable, and that is the point

It asserts the six resident slots hold exactly `17 … 22`.  I measured that at
round-0 entry rather than assuming it, and a frame whose slots held anything
else would make `shiftSupply_effect`'s `dup` branch push the wrong value and
break every template that uses it.  So unlike the premises this lane has had to
throw away — the tautological `mul_precondition`, the vacuous `∀ i, True`, the
underivable `WordOk.fits`, the inert `RegsOk` on the combine — this one has a
concrete failure mode and does real work.

It is also the only place the resident constants are pinned.  The literal-index
templates did not need it, because with a literal `v` the `dup` index was
concrete and the value came out of the frame variables directly.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStepFrame
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit

/-! ## 1.  Splitting an operation list -/

/-- Running a concatenation is running the parts in sequence.  This is what
lets a round be cut at its two rotation slots so the concrete stretches can
still be evaluated by reduction. -/
theorem runOps_append (memAt : UInt256 → UInt256) (l1 l2 : List Op)
    (s : List UInt256) :
    runOps memAt (l1 ++ l2) s = (runOps memAt l1 s).bind (runOps memAt l2) := by
  induction l1 generalizing s with
  | nil => rfl
  | cons o rest ih =>
      simp only [List.cons_append, runOps]
      cases runOp memAt o s with
      | none => rfl
      | some t => exact ih t

/-! ## 2.  The two branch-collapsing lemmas -/

/-- Both branches of `pushOffset` push the same value, so the artifact's choice
of `PUSH0` at the five zero-offset rounds does not change the semantics. -/
theorem pushOffset_effect (memAt : UInt256 → UInt256) (v : Nat)
    (stk : List UInt256) :
    runOp memAt (pushOffset v) stk = some (UInt256.ofNat v :: stk) := by
  unfold pushOffset
  by_cases h : v = 0
  · rw [if_pos h, h]
    rfl
  · rw [if_neg h]
    rfl

/-- The six resident rotation constants, pinned.  Falsifiable: a frame whose
slots held other values breaks `shiftSupply_effect`'s `dup` branch. -/
structure SuffixStd (sf : Suffix) : Prop where
  h17 : sf.s17 = UInt256.ofNat 17
  h18 : sf.s18 = UInt256.ofNat 18
  h19 : sf.s19 = UInt256.ofNat 19
  h20 : sf.s20 = UInt256.ofNat 20
  h21 : sf.s21 = UInt256.ofNat 21
  h22 : sf.s22 = UInt256.ofNat 22

/-- Both branches of `shiftSupply` push the rotation amount.  The `dup` branch
needs the resident constant to be where and what it should be, which is the
hypothesis; the `push` branch needs nothing. -/
theorem shiftSupply_effect (memAt : UInt256 → UInt256) (v : Nat)
    (stk : List UInt256)
    (hres : 17 ≤ v → v ≤ 22 → stk[v - 7]? = some (UInt256.ofNat v)) :
    runOp memAt (shiftSupply v) stk = some (UInt256.ofNat v :: stk) := by
  unfold shiftSupply
  by_cases h : 17 ≤ v ∧ v ≤ 22
  · rw [if_pos h]
    have hidx : v - 6 - 1 = v - 7 := by omega
    simp only [runOp, hidx, hres h.1 h.2, Option.map_some]
  · rw [if_neg h]
    rfl

/-- The rotation amounts that actually occur are in range, so the `dup`
branch's side condition is only ever asked about a real resident slot. -/
theorem shift_range (i : Nat) (_hi : i < 80) (hs : 0 < Crypto.Ripemd160.s[i]!)
    (hs32 : Crypto.Ripemd160.s[i]! < 32) :
    0 < 32 - Crypto.Ripemd160.s[i]! ∧ 32 - Crypto.Ripemd160.s[i]! < 32 := by
  omega

#print axioms runOps_append
#print axioms pushOffset_effect
#print axioms shiftSupply_effect
#print axioms shift_range

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
