import Challenge.Modexp.Submission.Proofs.Fast.Exp

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-!
# Interface for the fixed public-exponent route

The appended route recognizes exactly exponent 3 in one byte and exponent
65537 in three bytes. Every other exponent must reproduce the inherited
generic exponent-loop entry state. This module fixes those boundaries without
depending on concrete located paths.

This is an uncompiled source scaffold. It is instantiated only after the exact
cc628 artifact and relocated path tables have been generated.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs

/-- Exponent value as parsed by the MODEXP specification. -/
def exponentValue (input : ByteArray) (bsize esize : Nat) : Nat :=
  Precompile.bytesToNatPadded input (96 + bsize) esize

/-- Exact semantic cases recognized by the dispatcher. -/
inductive Case (input : ByteArray) (bsize esize : Nat) : Nat → Prop
  | three : esize = 1 → exponentValue input bsize esize = 3 →
      Case input bsize esize 1
  | fermat : esize = 3 → exponentValue input bsize esize = 65537 →
      Case input bsize esize 16

/-- The route handles precisely one of the two fixed addition chains. -/
def Matches (input : ByteArray) (bsize esize : Nat) : Prop :=
  ∃ count : Nat, Case input bsize esize count

/-- State after the replacement in `BDONE` jumps to the appended dispatcher
at pc 3179. -/
abbrev entryState (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  { Exp.bDone s mem n bsize esize msize with pc := UInt256.ofNat 3005 }

/-- Exact inherited exponent-loop state restored by every dispatcher miss. -/
abbrev missState (s : State) (mem : ByteArray)
    (n bsize esize msize : Nat) : State :=
  Exp.ebHead s (Exp.mcopyMem mem 1024 4096 (32 * n))
    n bsize esize msize 0

/-- Successful execution from the appended dispatcher. -/
abbrev Handled (input : ByteArray) (start : State) : Prop :=
  ∃ final : State,
    Nonempty (Challenge.EvmProof.GasSteps start final) ∧
      final.isDone = true ∧
      final.toResult = .returned (Challenge.Modexp.spec input)

/-- Concrete execution and semantic interface for the cc628 dispatcher. -/
structure Route (s : State) (mem input : ByteArray)
    (n bsize esize msize : Nat) where
  enter : Challenge.EvmProof.GasSteps
    (Exp.bDone s mem n bsize esize msize)
    (entryState s mem n bsize esize msize)
  miss : ¬ Matches input bsize esize → Challenge.EvmProof.GasSteps
    (entryState s mem n bsize esize msize)
    (missState s mem n bsize esize msize)
  hit : Matches input bsize esize →
    Handled input (entryState s mem n bsize esize msize)

end Challenge.Modexp.Submission.Proofs.Fast.FixedExponentRoute
