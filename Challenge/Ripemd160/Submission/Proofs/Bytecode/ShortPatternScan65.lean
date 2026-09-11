import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan65

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar

def doneState (input : ByteArray) : State :=
  exitState input 3 (scanAcc input 3)

def gasSteps_last (input : ByteArray) (hsize : input.size = 65) :
    GasSteps (compareState input 2 (scalarAt 2) (scanAcc input 2))
      (doneState input) :=
  gasSteps_compare_end input 2 (scalarAt 2) (scanAcc input 2)
    (by rw [hsize]; decide) (by omega)
    (by norm_num) (by decide) (by decide)

def gasSteps_scan (input : ByteArray) (hsize : input.size = 65) :
    GasSteps (patternedEntry input) (doneState input) := by
  have hfit : input.size < 2 ^ 256 := by rw [hsize]; decide
  have last : GasSteps (loopState input 2 (scanAcc input 2)) (doneState input) :=
    (sound wordPath (run_word_regular input 2 (scanAcc input 2)
      (by norm_num) (by decide))).trans (gasSteps_last input hsize)
  exact (sound setupPath (run_setup input)).trans
    ((gasStep0 input hfit (by rw [hsize]; decide)).trans ((gasStep1 input hfit (by rw [hsize]; decide)).trans last))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan65

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan65.gasSteps_last
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan65.gasSteps_scan
