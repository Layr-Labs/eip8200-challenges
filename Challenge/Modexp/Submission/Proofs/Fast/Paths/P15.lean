import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1768..1780).

`R1B` (pc 2539) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1768..1775, pc 2539..2911) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1776..1780, pc 2550..2921) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2309).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1768..1775, pc 2539..2911: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1550 .JUMPDEST,
   pushAt 1551 0 0,
   opAt 1552 .MLOAD,
   pushAt 1553 1 255,
   opAt 1554 .SHR,
   opAt 1555 .ISZERO,
   pushAt 1556 2 1594,
   opAt 1557 .JUMPI]

/-- Instructions 1776..1780, pc 2550..2921: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1558 1 1,
   pushAt 1559 2 8224,
   opAt 1560 .MSTORE,
   pushAt 1561 2 4653,
   opAt 1562 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
