import Challenge.Modexp.Submission.Proofs.Fast.CompactConstants
import Challenge.Modexp.Submission.Proofs.Fast.Model
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P11
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P12
import Challenge.Modexp.Submission.Proofs.Fast.Paths.P13
import Challenge.Modexp.Submission.Proofs.Fast.Paths.CsubFixed

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast

def ptrAt (base j : Nat) : Nat :=
  base + j * 115792089237316195423570985008687907853269984665640564039457584007913129639904

@[simp] theorem ptrAt_zero (base : Nat) : ptrAt base 0 = base := by
  simp [ptrAt]

end Challenge.Modexp.Submission.Proofs.Fast.Csub
