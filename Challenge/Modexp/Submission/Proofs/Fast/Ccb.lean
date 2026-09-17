import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P14
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-!
# Reachable CCB squaring loop

The width-selected CcbSeed entry establishes the squaring count and enters this
loop. The legacy single-doubling entry is absent from the selected bytecode.
This module proves the shared loop and return contracts used by the current
seed path against the actual instruction locations.
-/

namespace Challenge.Modexp.Submission.Proofs.Fast.Ccb

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

-- Lean 4.31 ships `List.getElem?_cons_zero` without the `simp` attribute, so the
-- program-counter tables of `Fast.Defs` (which end in `[…][i - lo]!`) do not
-- reduce inside the block-reduction `simp` calls without it.
attribute [local simp] List.getElem?_cons_zero


/-! ## States at the block boundaries -/

/-- The live part of the stack inside the loop: the counter, the block pointer
and the caller's return address. -/
def loopStack (px k : Nat) (ret : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat px, ret] ++ rest

/-- The loop head `CCL`, pc 2301, with the counter at `k`. -/
def loopState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1255
           stack := loopStack px k ret rest
           memory := mem }

/-- The `MONPRO` call, pc 2048, with the frame `[px, px, px, 2433]` pushed. -/
def mpCallState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 3205
           stack := [UInt256.ofNat px, UInt256.ofNat px, UInt256.ofNat px,
                     UInt256.ofNat 1266] ++ loopStack px k ret rest
           memory := mem }

/-- The return point, pc 2433, with the counter still at `k`. -/
def retState (s : State) (mem : ByteArray) (px k : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1266
           stack := loopStack px k ret rest
           memory := mem }

/-- The loop exit, pc 2400, with the counter at zero. -/
def exitState (s : State) (mem : ByteArray) (px : Nat) (ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1275
           stack := loopStack px 0 ret rest
           memory := mem }

/-- The indexed loop-head family: after `i` `MONPRO` calls the counter stands
at `8 - i`. -/
def loopFamily (s : State) (px : Nat) (ret : UInt256) (rest : List UInt256)
    (mems : Nat → ByteArray) (i : Nat) : State :=
  loopState s (mems i) px (8 - i) ret rest

