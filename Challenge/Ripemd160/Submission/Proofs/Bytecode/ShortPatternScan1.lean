import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan1
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar
def doneState (input : ByteArray) : State := exitState input 1 (scanAcc input 1)
def gasSteps_last (input : ByteArray) (hsize : input.size = 1) :
    GasSteps (compareState input 0 (scalarAt 0) (scanAcc input 0)) (doneState input) :=
  gasSteps_compare_end input 0 (scalarAt 0) (scanAcc input 0)
    (by rw [hsize]; decide) (by rw [hsize]; decide)
    (by norm_num) (by decide) (by decide)
def gasSteps_scan (input : ByteArray) (hsize : input.size = 1) :
    GasSteps (patternedEntry input) (doneState input) :=
  (sound setupPath (run_setup input)).trans
    ((sound wordPath (run_word_regular input 0 (scanAcc input 0)
      (by norm_num) (by decide))).trans (gasSteps_last input hsize))
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan1
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan1.gasSteps_scan
