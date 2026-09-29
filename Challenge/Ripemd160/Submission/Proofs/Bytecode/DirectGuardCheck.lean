import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The seed accumulator: reference word, anchor test, tail word and size test. -/

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

/-- The straight-line seed block from PC 39 to the loop head at PC 58. -/
def gasSteps_checkEntry (input : ByteArray) :
    GasSteps (sizeMatched input) (loopState input 0) := by
  let R := referenceWord input
  let W := MachineState.readWord input 968
  let f : UInt256 := R * UInt256.ofNat 255 + UInt256.ofNat 97
  rw [show sizeMatched input = PatternedScan.stS input 39 [] from rfl]
  have s0 := sS (pushAt 24 0 0) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 24 39 [] (by norm_num) pc_direct_24)
    (PatternedScan.stepS_push0 input 39 [] (by simp) (by norm_num)))
  have s1 := sS (opAt 25 .CALLDATALOAD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 25 40 [0] (by norm_num) pc_direct_25)
    (PatternedScan.stepS_calldataload input 40 0 [] (by simp) (by norm_num)))
  have s2 := sS (pushAt 26 2 960) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 26 41 [R] (by norm_num) pc_direct_26)
    (PatternedScan.stepS_push input 41 2 960 [R] (by simp) (by decide) (by decide) (by norm_num)))
  have s3 := sS (pushAt 27 1 97) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 27 44 [960, R] (by norm_num) pc_direct_27)
    (PatternedScan.stepS_push input 44 1 97 [960, R] (by simp) (by decide) (by decide) (by norm_num)))
  have s4 := sS (pushAt 28 1 255) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 28 46 [97, 960, R] (by norm_num) pc_direct_28)
    (PatternedScan.stepS_push input 46 1 255 [97, 960, R] (by simp) (by decide) (by decide) (by norm_num)))
  have s5 := sS (opAt 29 (.Dup ⟨3, by decide⟩)) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 29 48 [255, 97, 960, R] (by norm_num) pc_direct_29)
    (PatternedScan.stepS_dup input 48 3 (by decide) [255, 97, 960, R] R rfl (by simp) (by norm_num)))
  have s6 := sS (opAt 30 .MUL) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 30 49 [R, 255, 97, 960, R] (by norm_num) pc_direct_30)
    (PatternedScan.stepS_mul input 49 R 255 [97, 960, R] (by simp) (by norm_num)))
  have s7 := sS (opAt 31 .ADD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 31 50 [R * 255, 97, 960, R] (by norm_num) pc_direct_31)
    (PatternedScan.stepS_add input 50 (R * 255) 97 [960, R] (by simp) (by norm_num)))
  have s8 := sS (pushAt 32 2 968) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 32 51 [f, 960, R] (by norm_num) pc_direct_32)
    (PatternedScan.stepS_push input 51 2 968 [f, 960, R] (by simp) (by decide) (by decide) (by norm_num)))
  have s9 := sS (opAt 33 .CALLDATALOAD) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 33 54 [968, f, 960, R] (by norm_num) pc_direct_33)
    (PatternedScan.stepS_calldataload input 54 968 [f, 960, R] (by simp) (by norm_num)))
  have s10 := sS (opAt 34 (.Dup ⟨3, by decide⟩)) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 34 55 [W, f, 960, R] (by norm_num) pc_direct_34)
    (PatternedScan.stepS_dup input 55 3 (by decide) [W, f, 960, R] R rfl (by simp) (by norm_num)))
  have s11 := sS (opAt 35 .XOR) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 35 56 [R, W, f, 960, R] (by norm_num) pc_direct_35)
    (PatternedScan.stepS_xor input 56 R W [f, 960, R] (by simp) (by norm_num)))
  have s12 := sS (opAt 36 .OR) (PatternedScan.blockOfS _
    (PatternedScan.pcFactS input 36 57 [UInt256.xor R W, f, 960, R] (by norm_num) pc_direct_36)
    (PatternedScan.stepS_or input 57 (UInt256.xor R W) f [960, R] (by simp) (by norm_num)))
  have hend : PatternedScan.stS input (57 + 1) [UInt256.lor (UInt256.xor R W) f, 960, R] =
      loopState input 0 := rfl
  rw [hend] at s12
  exact s0.trans (s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans
    (s8.trans (s9.trans (s10.trans (s11.trans s12)))))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
