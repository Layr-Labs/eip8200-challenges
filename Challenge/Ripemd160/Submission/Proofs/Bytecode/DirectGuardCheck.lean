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

/-- The straight-line seed block from PC 33 and the `PUSH1 212 JUMP` at 45 to the loop head at PC 212. -/
def gasSteps_checkEntry (input : ByteArray) :
    GasSteps (sizeMatched input) (loopState input 0) := by
  let R := referenceWord input
  let W := MachineState.readWord input 968
  rw [show sizeMatched input = PatternedScan.stS input 34 [] from rfl]
  have s0 := sS (pushAt 19 0 0) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 19 34 [] (by norm_num) pc_direct_19)
    (PatternedScan.stepS_push0 input 34 [] (by simp) (by norm_num)))
  have s1 := sS (opAt 20 .CALLDATALOAD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 20 35 [0] (by norm_num) pc_direct_20)
    (PatternedScan.stepS_calldataload input 35 0 [] (by simp) (by norm_num)))
  have s2 := sS (pushAt 21 2 960) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 21 36 [R] (by norm_num) pc_direct_21)
    (PatternedScan.stepS_push input 36 2 960 [R] (by simp) (by decide) (by decide) (by norm_num)))
  have s3 := sS (pushAt 22 2 968) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 22 39 [960, R] (by norm_num) pc_direct_22)
    (PatternedScan.stepS_push input 39 2 968 [960, R] (by simp) (by decide) (by decide) (by norm_num)))
  have s4 := sS (opAt 23 .CALLDATALOAD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 23 42 [968, 960, R] (by norm_num) pc_direct_23)
    (PatternedScan.stepS_calldataload input 42 968 [960, R] (by simp) (by norm_num)))
  have s5 := sS (opAt 24 (.Dup ⟨2, by decide⟩)) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 24 43 [W, 960, R] (by norm_num) pc_direct_24)
    (PatternedScan.stepS_dup input 43 2 (by decide) [W, 960, R] R rfl (by simp) (by norm_num)))
  have s6 := sS (opAt 25 .XOR) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 25 44 [R, W, 960, R] (by norm_num) pc_direct_25)
    (PatternedScan.stepS_xor input 44 R W [960, R] (by simp) (by norm_num)))
  have p26 : Artifact.submissionArtifact.instructionPC 26 = 45 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have p27 : Artifact.submissionArtifact.instructionPC 27 = 47 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have hdest : Decode.isValidJumpDest submissionBytecode 212 = true := Artifact.validJumpDest_212
  have s7 := sS (pushAt 26 1 212) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 26 45 [UInt256.xor R W, 960, R] (by norm_num) p26)
    (PatternedScan.stepS_push input 45 1 212 [UInt256.xor R W, 960, R] (by simp) (by decide) (by decide) (by norm_num)))
  have s8 := sS (opAt 27 .JUMP) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 27 47 [212, UInt256.xor R W, 960, R] (by norm_num) p27)
    (PatternedScan.stepS_jump input 47 212 212 [UInt256.xor R W, 960, R] (by simp) (by norm_num) rfl hdest))
  have hend : PatternedScan.stS input 212 [UInt256.xor R W, 960, R] =
      loopState input 0 := rfl
  rw [hend] at s8
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8)))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
