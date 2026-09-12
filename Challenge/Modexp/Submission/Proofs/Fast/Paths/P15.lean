import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1898..1910).

`R1B` (pc 2677) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1898..1905, pc 2677..3049) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1824..1910, pc 2688..3018) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2435).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1898..1905, pc 2677..3049: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1625 .JUMPDEST,
   pushAt 1626 0 0,
   opAt 1627 .MLOAD,
   pushAt 1628 1 255,
   opAt 1629 .SHR,
   opAt 1630 .ISZERO,
   pushAt 1631 2 1728,
   opAt 1632 .JUMPI]

/-- Instructions 1824..1910, pc 2688..3018: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1633 1 1,
   pushAt 1634 2 4128,
   opAt 1635 .MSTORE,
   pushAt 1636 2 4885,
   opAt 1637 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
