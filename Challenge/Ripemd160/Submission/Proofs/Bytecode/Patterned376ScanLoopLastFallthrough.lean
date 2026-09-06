import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanState

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.all false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

theorem run_loop_fallthrough (input : ByteArray) :
    run loopJumpPath (loopBranchState input) = some (loopExitState input) := by
  simp [loopJumpPath, opAt, loopBranchState, loopExitState,
    UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376Scan
