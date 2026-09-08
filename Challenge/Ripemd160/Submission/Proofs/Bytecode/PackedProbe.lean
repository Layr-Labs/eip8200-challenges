import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedRound0

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 80000
set_option maxHeartbeats 8000000

/-!
# Composition probe: group 2, even phase, parameterised

The literal templates are proved.  This is the first template stated over the
round's DATA rather than its index - the two message offsets and the two
rotation amounts are variables - so it covers all eight rounds of its class
rather than one.  Group 2 even is the probe because its body is the shortest at
38 operations, so a failure here is the smallest failure to read.

## The parameterised case is EASIER than the literal one, and nobody should
## "simplify" it back

`packedRot` is written `UInt256.ofNat (32 - sl)`, not with a numeral, and
`shiftSupply` produces the same derived form.  At a symbolic index the two sides
therefore match DIRECTLY.  It was the literal index that needed a `rfl` bridge,
because there `21` met `32 - 11`.  So `32 - s` is carried unreduced end to end
here on purpose.  Reducing it to a numeral reintroduces exactly the mismatch
that cost a rebuild in `slot2_outer`.

## The residents are literals, not variables

`shiftSupply_site` below is hypothesis-free because the six rotation constants
appear in the stack as `UInt256.ofNat 17 … 22` rather than as opaque slots.
That is exactly what `SuffixStd` asserts, so a caller rewrites the frame into
this form once and the site lemma then applies with no side condition - instead
of every use carrying `stk[v - 7]? = some (UInt256.ofNat v)`.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric

/-! ## Per-opcode reduction

`runOp` is deliberately NOT given to `simp` below.  It is a `match` on the
opcode, so unfolding it against a symbolic op — `pushOffset lo`, which is an
`if` — produces a match on a scrutinee simp cannot resolve, and it stops there.
That is exactly what happened on the first attempt.

These twelve lemmas give `simp` a reduction for each CONCRETE opcode and none
for a symbolic one, so at the four symbolic sites the only applicable rewrites
are `pushOffset_effect` and `shiftSupply_site`.  The staging is enforced by what
is available rather than by rewrite order.
-/

@[simp] theorem runOp_push0 (memAt : UInt256 → UInt256) (s : List UInt256) :
    runOp memAt Op.push0 s = some (0 :: s) := rfl

@[simp] theorem runOp_push (memAt : UInt256 → UInt256) (v : UInt256)
    (s : List UInt256) : runOp memAt (Op.push v) s = some (v :: s) := rfl

@[simp] theorem runOp_mload (memAt : UInt256 → UInt256) (x : UInt256)
    (s : List UInt256) :
    runOp memAt Op.mload (x :: s) = some (memAt x :: s) := rfl

@[simp] theorem runOp_dup (memAt : UInt256 → UInt256) (n : Nat)
    (s : List UInt256) :
    runOp memAt (Op.dup n) s = (s[n - 1]?).map (fun v => v :: s) := rfl

@[simp] theorem runOp_swap (memAt : UInt256 → UInt256) (n : Nat) (x : UInt256)
    (s : List UInt256) :
    runOp memAt (Op.swap n) (x :: s)
      = (s[n - 1]?).map (fun v => v :: s.set (n - 1) x) := rfl

@[simp] theorem runOp_pop (memAt : UInt256 → UInt256) (x : UInt256)
    (s : List UInt256) : runOp memAt Op.pop (x :: s) = some s := rfl

@[simp] theorem runOp_and (memAt : UInt256 → UInt256) (x y : UInt256)
    (s : List UInt256) :
    runOp memAt Op.and (x :: y :: s) = some ((x &&& y) :: s) := rfl

@[simp] theorem runOp_or (memAt : UInt256 → UInt256) (x y : UInt256)
    (s : List UInt256) :
    runOp memAt Op.or (x :: y :: s) = some ((x ||| y) :: s) := rfl

@[simp] theorem runOp_xor (memAt : UInt256 → UInt256) (x y : UInt256)
    (s : List UInt256) :
    runOp memAt Op.xor (x :: y :: s) = some ((x ^^^ y) :: s) := rfl

@[simp] theorem runOp_add (memAt : UInt256 → UInt256) (x y : UInt256)
    (s : List UInt256) :
    runOp memAt Op.add (x :: y :: s) = some ((x + y) :: s) := rfl

@[simp] theorem runOp_mul (memAt : UInt256 → UInt256) (x y : UInt256)
    (s : List UInt256) :
    runOp memAt Op.mul (x :: y :: s) = some ((x * y) :: s) := rfl

@[simp] theorem runOp_shr (memAt : UInt256 → UInt256) (x y : UInt256)
    (s : List UInt256) :
    runOp memAt Op.shr (x :: y :: s)
      = some (UInt256.shiftRight y x :: s) := rfl

/-- A rotation amount pushed at a round's shift site.  Both branches of
`shiftSupply` push `UInt256.ofNat v`; the `dup` branch reads index `v - 7`,
which is where the residents sit at every one of the four sites. -/
theorem shiftSupply_site (memAt : UInt256 → UInt256) (v : Nat)
    (X Y b c d e mLR mL mR cM : UInt256) (tl : List UInt256) :
    runOp memAt (shiftSupply v)
        (X :: Y :: b :: c :: d :: e :: mLR :: mL :: mR :: cM ::
          UInt256.ofNat 17 :: UInt256.ofNat 18 :: UInt256.ofNat 19 ::
          UInt256.ofNat 20 :: UInt256.ofNat 21 :: UInt256.ofNat 22 :: tl)
      = some (UInt256.ofNat v :: X :: Y :: b :: c :: d :: e :: mLR :: mL ::
          mR :: cM :: UInt256.ofNat 17 :: UInt256.ofNat 18 ::
          UInt256.ofNat 19 :: UInt256.ofNat 20 :: UInt256.ofNat 21 ::
          UInt256.ofNat 22 :: tl) := by
  apply shiftSupply_effect
  intro h1 h2
  interval_cases v <;> rfl

/- `bodyEven2_exec` REMOVED: its single `simp` exhausted a 6 GB cap.
Replaced by the segment-cut route in `PackedProbeCut`.  See PLAYBOOK 134:
`simp only` with a named list carries no simprocs, so the literal DUP index
cannot reduce there at all — the fix is structural, not a narrower set. -/

#print axioms shiftSupply_site

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe
