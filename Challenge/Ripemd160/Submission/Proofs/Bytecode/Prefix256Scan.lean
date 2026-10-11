import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Scan
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedInputData PatternedSwar

def doneState (input : ByteArray) : State :=
  exitState input 12 (scanAcc input 12)

def gasSteps_last (input : ByteArray) (hsize : input.size = 376) :
    GasSteps (compareState input 11 (scalarAt 11) (scanAcc input 11))
      (doneState input) :=
  gasSteps_compare_end input 11 (scalarAt 11) (scanAcc input 11)
    (by rw [hsize]; decide) (by rw [hsize]; decide)
    (by norm_num) (by decide) (by decide)

def gasSteps_scan (input : ByteArray) (hsize : input.size = 376) :
    GasSteps (patternedEntry input) (doneState input) := by
  have hfit : input.size < 2 ^ 256 := by rw [hsize]; decide
  have last : GasSteps (loopState input 11 (scanAcc input 11)) (doneState input) :=
    (sound wordPath (run_word_regular input 11 (scanAcc input 11)
      (by norm_num) (by decide))).trans (gasSteps_last input hsize)
  exact (sound setupPath (run_setup input)).trans ((gasStep0 input hfit (by rw [hsize]; decide)).trans ((gasStep1 input hfit (by rw [hsize]; decide)).trans ((gasStep2 input hfit (by rw [hsize]; decide)).trans ((gasStep3 input hfit (by rw [hsize]; decide)).trans ((gasStep4 input hfit (by rw [hsize]; decide)).trans ((gasStep5 input hfit (by rw [hsize]; decide)).trans ((gasStep6 input hfit (by rw [hsize]; decide)).trans ((gasStep7 input hfit (by rw [hsize]; decide)).trans ((gasStep8 input hfit (by rw [hsize]; decide)).trans ((gasStep9 input hfit (by rw [hsize]; decide)).trans ((gasStep10 input hfit (by rw [hsize]; decide)).trans (last))))))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Scan
