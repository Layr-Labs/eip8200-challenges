import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128GuardTrace
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The appended 128-byte guard and its bridge into the patterned scan. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

abbrev Located := DirectGuard.Located

private def sound (path : List Located) {s t : State}
    (h : DirectGuard.run path s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    path hcode hfork h hrun hnp

/- The failure path stops at JUMPI.  It must not include the success suffix:
   a taken JUMPI changes the PC to 368, so the next located instruction would
   fail the PC check. -/
private def guardCheckPath : List Located :=
  [DirectGuard.opAt 4116 .JUMPDEST,
   DirectGuard.opAt 4117 .CALLDATASIZE,
   DirectGuard.pushAt 4118 1 128,
   DirectGuard.opAt 4119 .XOR,
   DirectGuard.opAt 4120 .JUMPDEST,
   DirectGuard.pushAt 4121 0 0,
   DirectGuard.opAt 4122 .CALLDATALOAD,
   DirectGuard.pushAt 4123 0 0,
   DirectGuard.opAt 4124 .BYTE,
   DirectGuard.pushAt 4125 1 7,
   DirectGuard.opAt 4126 .XOR,
   DirectGuard.opAt 4127 .JUMPDEST,
   DirectGuard.opAt 4128 .OR,
   DirectGuard.pushAt 4129 2 368,
   DirectGuard.opAt 4130 .JUMPI]

private def guardMatchSuffix : List Located :=
  [DirectGuard.pushAt 4131 0 0,
   DirectGuard.pushAt 4132 1 101,
   DirectGuard.opAt 4133 .JUMP]

private def guardMatchTail : List Located :=
  [DirectGuard.opAt 61 .JUMPDEST, DirectGuard.opAt 62 .POP]

private def guardJumpState (input : ByteArray) : State :=
  { DirectGuard.guardEntry input with
    pc := UInt256.ofNat 101
    stack := [UInt256.ofNat 0] }

private theorem run_guard_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    DirectGuard.run guardCheckPath (DirectGuard.guardEntry input) =
      some (DirectGuard.fallbackState input) := by
  exact Patterned128GuardTrace.run_guard_fail input hfit hbad

private theorem run_guard_match_helper (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    DirectGuard.run (guardCheckPath ++ guardMatchSuffix)
      (DirectGuard.guardEntry input) = some (guardJumpState input) := by
  exact Patterned128GuardTrace.run_guard_match_helper input hfit hsize hbyte

private theorem run_guard_match_tail (input : ByteArray) :
    DirectGuard.run guardMatchTail (guardJumpState input) =
      some (PatternedScan.patternedEntry input) := by
  simp (config := { decide := true })
    [guardMatchTail, DirectGuard.opAt, DirectGuard.pushAt, DirectGuard.wfOp,
     guardJumpState, DirectGuard.guardEntry, PatternedScan.patternedEntry,
     DirectGuard.atPC, PatternedScan.atPC,
     Challenge.EvmProof.Stepper.runLocatedBlock,
     Challenge.EvmProof.Stepper.runLocated,
     Challenge.EvmProof.Stepper.runInstr,
     Challenge.EvmProof.Word.succ_ofNat_mod]

def gasSteps_fail (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7) :
    GasSteps (DirectGuard.guardEntry input) (DirectGuard.fallbackState input) :=
  sound guardCheckPath (run_guard_fail input hfit hbad)

def gasSteps_match (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (DirectGuard.guardEntry input) (PatternedScan.patternedEntry input) :=
  (sound (guardCheckPath ++ guardMatchSuffix)
      (run_guard_match_helper input hfit hsize hbyte)).trans
    (sound guardMatchTail (run_guard_match_tail input))

def gasSteps_hit (input : ByteArray) (hfit : CalldataFits input)
    (hsize : input.size = 128) (hbyte : DirectGuard.firstByte input = 7) :
    GasSteps (initialState submissionBytecode input 0)
      (PatternedScan.patternedEntry input) := by
  have h1000 : input.size ≠ 1000 := by omega
  have h376 : input.size ≠ 376 := by omega
  have h256 : input.size ≠ 256 := by omega
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_match input hfit hsize hbyte))

def gasSteps_miss (input : ByteArray) (hfit : CalldataFits input)
    (hbad : input.size ≠ 128 ∨ DirectGuard.firstByte input ≠ 7)
    (h1000 : input.size ≠ 1000) (h376 : input.size ≠ 376)
    (h256 : input.size ≠ 256) :
    GasSteps (initialState submissionBytecode input 0)
      (DirectGuard.fallbackState input) := by
  exact (Execution.gasSteps_start input).trans
    ((sound DirectGuard.sizePath
        (DirectGuard.run_size_fail input hfit h1000 h376 h256)).trans
      (gasSteps_fail input hfit hbad))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned128Entry
