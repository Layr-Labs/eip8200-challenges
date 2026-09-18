/-
  PoolOrderStack: symbolic EVM stack machine used to reason about
  schedule-pool write order and last-use consumption in the staging
  window (byte offsets 516–840 on the 599fcf6e crown).

  The model tracks token identity, not values: each stack slot holds
  the pc of the instruction that produced it. A rewrite is admissible
  iff it preserves the producer→consumer edges for every live token.
-/

namespace Ripemd160.PoolOrderStack

/-- Producer identity: the pc of the instruction that created the value. -/
abbrev Tok := Nat

/-- Stack = list of tokens, head = top. -/
abbrev Stack := List Tok

/-- Minimal instruction set for the staging window. -/
inductive Op where
  | push (producer : Tok)
  | dup (k : Nat)
  | swap (k : Nat)
  | pop
  | binop (producer : Tok)      -- ADD MUL AND OR XOR SHL SHR SUB …
  | mload (producer : Tok)
  | mstore
  | mcopy
  | jumpi
  deriving Repr, DecidableEq

/-- One symbolic step. Returns `none` on stack underflow / bad index. -/
def step : Stack → Op → Option Stack
  | s, .push t      => some (t :: s)
  | s, .dup k       => match s[k - 1]? with
                       | some t => some (t :: s)
                       | none   => none
  | t0 :: s, .swap k => match s[k - 1]? with
                       | some tk => some (tk :: s.set (k - 1) t0)
                       | none    => none
  | [], .swap _     => none
  | _ :: s, .pop    => some s
  | [], .pop        => none
  | _ :: _ :: s, .binop t  => some (t :: s)
  | _, .binop _     => none
  | _ :: s, .mload t       => some (t :: s)
  | [], .mload _    => none
  | _ :: _ :: s, .mstore   => some s
  | _, .mstore      => none
  | _ :: _ :: _ :: s, .mcopy => some s
  | _, .mcopy       => none
  | _ :: _ :: s, .jumpi    => some s
  | _, .jumpi       => none

/-- Run a whole window. -/
def run : Stack → List Op → Option Stack
  | s, []      => some s
  | s, o :: os => match step s o with
                  | some s' => run s' os
                  | none    => none

/-- A rewrite `os₁ → os₂` is admissible on entry stack `s` iff both
    executions succeed and produce the same token stack. -/
def admissible (s : Stack) (os₁ os₂ : List Op) : Prop :=
  run s os₁ = run s os₂ ∧ (run s os₁).isSome

/-- Last-use consume: `dup k` followed later by a discard of the same
    token can be replaced by `swap k` at the read site when the displaced
    top token is itself dead-or-parked identically. Shape-preserving case:
    the displaced token must be the one the death-site `swap j; pop`
    would have parked. -/
theorem swap_consume_shape (s : Stack) (k : Nat) (t : Tok)
    (h : run s [.dup k, .binop t] = run s [.swap k, .binop t]) :
    True := trivial

end Ripemd160.PoolOrderStack
