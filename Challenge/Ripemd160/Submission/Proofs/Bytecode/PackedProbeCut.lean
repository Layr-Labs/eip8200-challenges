import Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe

set_option warningAsError true
set_option autoImplicit false
set_option maxRecDepth 80000
set_option maxHeartbeats 8000000

/-!
# The composition probe, cut at the four symbolic sites

The single-`simp` version exhausted 6 GB.  The cause was mine: I widened
`simp only` to `simp` to pick up `Option.bind_some`, which put the whole default
set in scope over 43 operations on a 19-cell stack.

Narrowing it back is not enough on its own, and the reason is worth recording.
An explicit `simp only` set cannot finish this, because `runOp_dup` produces
`s[n - 1]?` with `n` a LITERAL, and the core lemma is
`getElem?_cons_succ : (a :: l)[i + 1]? = l[i]?`, which needs `15` matched
against `?i + 1`.  That match is done by a numeral simproc, not by a lemma, and
`simp only` with a named list does not carry simprocs.  So the choice is not
"wide simp versus narrow simp" — a narrow one cannot reduce the index at all.

The cut removes the need.  Each stretch between two symbolic opcodes is fully
concrete, so `runOps` over it reduces in the kernel, where a literal index is no
obstacle, and is closed by `rfl` rather than by rewriting.  `runOps_append` was
built for exactly this and this is the first time it has been needed.

STATUS: WRITTEN, NOT ELABORATED.  Axiom status unknown until built.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeCut

open EvmSemantics
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedStep0
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedEmit
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedTemplateGeneric
open Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbe

/-- A one-operation list runs that operation. -/
theorem runOps_singleton (memAt : UInt256 → UInt256) (o : Op)
    (s : List UInt256) : runOps memAt [o] s = runOp memAt o s := by
  -- The `show` is the whole fix.  Without it the goal is `runOps memAt [o] s`,
  -- which contains no syntactic occurrence of `runOp memAt o s`, so `cases`
  -- abstracts nothing and `rfl` is left facing the unreduced application.
  show (runOp memAt o s).bind (runOps memAt []) = runOp memAt o s
  cases h : runOp memAt o s with
  | none => rfl
  | some t => rfl

/-- Concrete stretch 0: 1 operations, no symbolic opcode. -/
def seg0 : List Op :=
  [Op.mload]

/-- Concrete stretch 1: 18 operations, no symbolic opcode. -/
def seg1 : List Op :=
  [Op.mload, Op.or, Op.dup 4, Op.dup 8, Op.xor, Op.dup 4, Op.or, Op.dup 6,
   Op.xor, Op.add, Op.add, Op.dup 16, Op.add, Op.dup 6, Op.and, Op.dup 9,
   Op.mul, Op.dup 1]

/-- Concrete stretch 2: 4 operations, no symbolic opcode. -/
def seg2 : List Op :=
  [Op.shr, Op.dup 8, Op.and, Op.swap 1]

/-- The second concrete stretch in the explicit cons form required by the
following symbolic `shiftSupply` site.  Naming this result prevents Lean from
leaving the `SWAP1` result as an opaque `List.set` term during unification. -/
theorem seg2_effect (memAt : UInt256 → UInt256) (v : Nat)
    (X Y b c d e mLR mL : UInt256) (tail : List UInt256) :
    runOps memAt seg2
        (UInt256.ofNat v :: X :: Y :: b :: c :: d :: e :: mLR :: mL :: tail)
      = some (Y :: (mL &&& UInt256.shiftRight X (UInt256.ofNat v)) :: b :: c ::
          d :: e :: mLR :: mL :: tail) := rfl

/-- Concrete stretch 3: 16 operations, no symbolic opcode. -/
def seg3 : List Op :=
  [Op.shr, Op.dup 9, Op.and, Op.or, Op.dup 5, Op.add, Op.swap 2, Op.dup 6,
   Op.and, Op.dup 9, Op.mul, Op.dup 15, Op.shr, Op.dup 6, Op.and, Op.swap 4]

/-- The round, cut at its four symbolic opcodes.  `rfl` because the cut is a
regrouping of the same list.

Right-nested deliberately: `++` is left-associative, so a flat chain would make
`runOps_append` peel the LAST segment first and nest the binds backwards.
Nesting to the right makes each peel take the next symbolic opcode off the
front, which is the order the effect lemmas want. -/
theorem bodyEven2_cut (lo hi vl vr : Nat) :
    pushOffset lo :: Op.mload :: pushOffset hi :: Op.mload :: Op.or ::
        bodyEven2 (shiftSupply vl) (shiftSupply vr)
      = pushOffset lo :: (seg0 ++ (pushOffset hi :: (seg1
        ++ (shiftSupply vl :: (seg2 ++ (shiftSupply vr :: seg3)))))) := rfl

/-- Peel one operation whose effect is known.  Covers both a concrete opcode
(where the effect is `rfl`) and a symbolic one (where it is an effect lemma),
and needs no `Option` lemma by name — the `show` makes the bind visible and the
rewrite of `h` lets it reduce. -/
theorem runOps_cons_effect (memAt : UInt256 → UInt256) (o : Op) (l : List Op)
    (s t : List UInt256) (h : runOp memAt o s = some t) :
    runOps memAt (o :: l) s = runOps memAt l t := by
  show (runOp memAt o s).bind (runOps memAt l) = runOps memAt l t
  rw [h]
  rfl

/-- Peel a whole concrete stretch whose result is known.  Used with `rfl`, so
the stretch is reduced by the kernel rather than searched by a tactic. -/
theorem runOps_seg (memAt : UInt256 → UInt256) (l1 l2 : List Op)
    (s t : List UInt256) (h : runOps memAt l1 s = some t) :
    runOps memAt (l1 ++ l2) s = runOps memAt l2 t := by
  rw [runOps_append, h]
  rfl

#print axioms runOps_singleton
#print axioms seg2_effect
#print axioms runOps_cons_effect
#print axioms runOps_seg
#print axioms bodyEven2_cut

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedProbeCut
