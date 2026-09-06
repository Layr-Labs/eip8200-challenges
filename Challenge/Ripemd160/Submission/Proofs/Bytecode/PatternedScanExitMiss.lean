import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem run_exit_miss (input : ByteArray) (hne : scanAcc input 1000 ≠ 0) :
    run exitPath (loopExitState input) = some (fallbackState input) := by
  have htrue : UInt256.isTrue (scanAcc input 1000) := by
    intro hz
    apply hne
    apply Challenge.EvmProof.Word.word_ext
    simpa only [show (0 : UInt256).toNat = 0 by rfl] using hz
  have hneNat : (scanAcc input 1000).toNat ≠ 0 := htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 1006 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 682 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [exitPath, opAt, pushAt, wfOp, loopExitState, fallbackState,
    atPC, htrue, hneNat, hdest, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
