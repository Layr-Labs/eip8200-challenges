import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1799..1811).

`R1B` (pc 2945) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1799..1806, pc 2945..2955) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1807..1811, pc 2956..2965) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2686).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1768`, now instructions 1799..1806, pc 2945..2955: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1799 .JUMPDEST,
   pushAt 1800 0 0,
   opAt 1801 .MLOAD,
   pushAt 1802 1 255,
   opAt 1803 .SHR,
   opAt 1804 .ISZERO,
   pushAt 1805 2 1911,
   opAt 1806 .JUMPI]

/-- Original block `1776`, now instructions 1807..1811, pc 2956..2965: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1807 1 1,
   pushAt 1808 2 8224,
   opAt 1809 .MSTORE,
   pushAt 1810 2 2686,
   opAt 1811 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
