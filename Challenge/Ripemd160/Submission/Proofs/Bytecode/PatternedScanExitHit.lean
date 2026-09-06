import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem run_exit_hit (input : ByteArray) (hz : scanAcc input 1000 = 0) :
    run exitPath (loopExitState input) = some (hitEntry input) := by
  have hfalse : ¬ UInt256.isTrue (scanAcc input 1000) := by
    rw [hz]
    decide
  simp (config := { maxSteps := 1000000 })
    [exitPath, opAt, pushAt, wfOp, loopExitState, hitEntry, atPC, hz, hfalse,
    UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
