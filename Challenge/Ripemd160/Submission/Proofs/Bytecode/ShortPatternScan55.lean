import Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan55

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar

def doneState (input : ByteArray) : State :=
  exitState input 2 (scanAcc input 2)

def gasSteps_last (input : ByteArray) (hsize : input.size = 55) :
    GasSteps (compareState input 1 (scalarAt 1) (scanAcc input 1))
      (doneState input) :=
  gasSteps_compare_end input 1 (scalarAt 1) (scanAcc input 1)
    (by rw [hsize]; decide) (by omega)
    (by norm_num) (by decide) (by decide)

def gasSteps_scan (input : ByteArray) (hsize : input.size = 55) :
    GasSteps (patternedEntry input) (doneState input) := by
  have hfit : input.size < 2 ^ 256 := by rw [hsize]; decide
  have last : GasSteps (loopState input 1 (scanAcc input 1)) (doneState input) :=
    (sound wordPath (run_word_regular input 1 (scanAcc input 1)
      (by norm_num) (by decide))).trans (gasSteps_last input hsize)
  exact (sound setupPath (run_setup input)).trans
    ((gasStep0 input hfit (by rw [hsize]; decide)).trans last)


end Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan55

#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan55.gasSteps_last
#print axioms Challenge.Ripemd160.Submission.Proofs.Bytecode.ShortPatternScan55.gasSteps_scan
