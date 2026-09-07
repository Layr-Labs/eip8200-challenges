import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1793..1805).

`R1B` (pc 2930) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1793..1800, pc 2930..2940) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1801..1805, pc 2941..2950) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2671).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Original block `1768`, now instructions 1793..1800, pc 2930..2940: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1793 .JUMPDEST,
   pushAt 1794 0 0,
   opAt 1795 .MLOAD,
   pushAt 1796 1 255,
   opAt 1797 .SHR,
   opAt 1798 .ISZERO,
   pushAt 1799 2 1911,
   opAt 1800 .JUMPI]

/-- Original block `1776`, now instructions 1801..1805, pc 2941..2950: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1801 1 1,
   pushAt 1802 2 8224,
   opAt 1803 .MSTORE,
   pushAt 1804 2 2671,
   opAt 1805 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
