import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
/-! Basic-block instruction paths, group 15 (instructions 1895..1907).

`R1B` (pc 2674) sits in front of the first `DOUBLE256` call.  When the
modulus's most significant bit is set, `radix ^ n < 2 * m`, so `R mod m` is
just `radix ^ n - m` — one borrow-propagating subtraction.  `CSUB` already
computes `t[n] * radix ^ n + t_low - m` selected against `m`, so storing
`t[n] := 1` over the still-zero `t` block and entering `CSUB` with `pd = R1`
produces `R mod m` in a single pass over the limbs instead of the 256 modular
doublings `DOUBLE256` performs.  Every other modulus falls through to
`DOUBLE256` unchanged.

The two basic blocks are

* `blk1768` (idx 1895..1902, pc 2674..3046) — `JUMPDEST`, the top-bit test
  `MLOAD 0; PUSH1 255; SHR; ISZERO` and the `JUMPI` back to `DOUBLE256`;
* `blk1776` (idx 1824..1907, pc 2688..3015) — `MSTORE TN 1` and the tail call
  into `CSUB` (pc 2432).

Both leave the incoming stack `[px, ret]` exactly as `DOUBLE256` and `CSUB`
expect it, so neither call site moves. -/

namespace Challenge.Modexp.Submission.Proofs.Fast

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Instructions 1895..1902, pc 2674..3046: the top-bit test and the branch
back into `DOUBLE256`. -/
def blk1768 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1180 .JUMPDEST,
   pushAt 1181 0 0,
   opAt 1182 .MLOAD,
   pushAt 1183 1 255,
   opAt 1184 .SHR,
   opAt 1185 .ISZERO,
   pushAt 1186 2 1175,
   opAt 1187 .JUMPI]

/-- Instructions 1824..1907, pc 2688..3015: `t[n] := 1` and the tail call into
`CSUB`. -/
def blk1776 :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1188 1 1,
   pushAt 1189 2 2080,
   opAt 1190 .MSTORE,
   pushAt 1191 2 4338,
   opAt 1192 .JUMP]

end Challenge.Modexp.Submission.Proofs.Fast
