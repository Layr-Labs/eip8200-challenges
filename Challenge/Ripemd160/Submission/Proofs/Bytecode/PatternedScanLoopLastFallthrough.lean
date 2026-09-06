import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanState

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def loopJumpPath : List Located := [opAt 2892 .JUMPI]

def loopBranchState (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 4971
    stack := [UInt256.ofNat 4933, 0, scanAcc input 1000, UInt256.ofNat 1000] }

theorem run_loop_fallthrough (input : ByteArray) :
    run loopJumpPath (loopBranchState input) = some (loopExitState input) := by
  simp [loopJumpPath, opAt, loopBranchState, loopExitState,
    UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, initialState,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
