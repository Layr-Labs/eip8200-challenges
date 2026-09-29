import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The seed accumulator: reference word and tail word. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private def sS (l : Located) {s t : State}
    (h : Challenge.EvmProof.DataStepper.runLocatedBlock [l] s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    [l] hcode hfork h hrun hnp

/-- The straight-line seed block from PC 30 to the loop head at PC 41. -/
def gasSteps_checkEntry (input : ByteArray) :
    GasSteps (sizeMatched input) (loopState input 0) := by
  let R := referenceWord input
  let W := MachineState.readWord input 968
  rw [show sizeMatched input = PatternedScan.stS input 30 [] from rfl]
  have s0 := sS (pushAt 19 0 0) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 19 30 [] (by norm_num) pc_direct_19)
    (PatternedScan.stepS_push0 input 30 [] (by simp) (by norm_num)))
  have s1 := sS (opAt 20 .CALLDATALOAD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 20 31 [0] (by norm_num) pc_direct_20)
    (PatternedScan.stepS_calldataload input 31 0 [] (by simp) (by norm_num)))
  have s2 := sS (pushAt 21 2 960) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 21 32 [R] (by norm_num) pc_direct_21)
    (PatternedScan.stepS_push input 32 2 960 [R] (by simp) (by decide) (by decide) (by norm_num)))
  have s3 := sS (pushAt 22 2 968) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 22 35 [960, R] (by norm_num) pc_direct_22)
    (PatternedScan.stepS_push input 35 2 968 [960, R] (by simp) (by decide) (by decide) (by norm_num)))
  have s4 := sS (opAt 23 .CALLDATALOAD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 23 38 [968, 960, R] (by norm_num) pc_direct_23)
    (PatternedScan.stepS_calldataload input 38 968 [960, R] (by simp) (by norm_num)))
  have s5 := sS (opAt 24 (.Dup ⟨2, by decide⟩)) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 24 39 [W, 960, R] (by norm_num) pc_direct_24)
    (PatternedScan.stepS_dup input 39 2 (by decide) [W, 960, R] R rfl (by simp) (by norm_num)))
  have s6 := sS (opAt 25 .XOR) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 25 40 [R, W, 960, R] (by norm_num) pc_direct_25)
    (PatternedScan.stepS_xor input 40 R W [960, R] (by simp) (by norm_num)))
  have hend : PatternedScan.stS input (40 + 1) [UInt256.xor R W, 960, R] =
      loopState input 0 := rfl
  rw [hend] at s6
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6)))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
