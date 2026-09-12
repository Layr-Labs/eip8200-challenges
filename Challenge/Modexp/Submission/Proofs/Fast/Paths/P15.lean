import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1893..1905).

`R1B` (pc 2672) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1893..1900, pc 2672..3044) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1824..1905, pc 2688..3013) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2430).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1893..1900, pc 2672..3044: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1622 .JUMPDEST,
   pushAt 1623 0 0,
   opAt 1624 .MLOAD,
   pushAt 1625 1 255,
   opAt 1626 .SHR,
   opAt 1627 .ISZERO,
   pushAt 1628 2 1723,
   opAt 1629 .JUMPI]

/-- Instructions 1824..1905, pc 2688..3013: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1630 1 1,
   pushAt 1631 2 4128,
   opAt 1632 .MSTORE,
   pushAt 1633 2 4875,
   opAt 1634 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
