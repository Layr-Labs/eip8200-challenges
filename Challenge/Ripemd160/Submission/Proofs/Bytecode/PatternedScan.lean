import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanReturn
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanGate

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The scalar-SWAR patterned-1000 guard, end to end

The setup pushes the five constants, the scan folds thirty-one words and the
padded tail into one accumulator, and the accumulator decides between the
stored answer and the program.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar

def gasSteps_fromEntry_hit (input : ByteArray) (hsize : input.size = 1000)
    (hz : scanAccFinal input = 0) (h7 : PatternedScanGate.firstByte input = 7) :
    GasSteps (patternedEntry input) (returnedState input) :=
  (PatternedScanGate.gasSteps_pass input h7).trans
    ((sound setupPath (run_setup input)).trans
      ((gasSteps_scan input hsize).trans
        ((gasSteps_tail_hit input hz).trans
          (by
            have h := (scanAccFinal_zero_iff_eq input hsize).1 hz
            subst input
            exact gasSteps_return))))

def gasSteps_fromEntry_miss (input : ByteArray) (hsize : input.size = 1000)
    (hne : scanAccFinal input ≠ 0) (h7 : PatternedScanGate.firstByte input = 7) :
    GasSteps (patternedEntry input) (fallbackState input) :=
  (PatternedScanGate.gasSteps_pass input h7).trans
    ((sound setupPath (run_setup input)).trans
      ((gasSteps_scan input hsize).trans (gasSteps_tail_miss input hne)))

def gasSteps_patterned :
    GasSteps (patternedEntry patternedInput) (returnedState patternedInput) :=
  gasSteps_fromEntry_hit patternedInput patternedInput_size scanAccFinal_patterned
    PatternedScanGate.patterned_firstByte

def gasSteps_patterned_miss (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ patternedInput) :
    GasSteps (patternedEntry input) (fallbackState input) := by
  by_cases h7 : PatternedScanGate.firstByte input = 7
  · exact gasSteps_fromEntry_miss input hsize (fun hz =>
      hne ((scanAccFinal_zero_iff_eq input hsize).1 hz)) h7
  · exact PatternedScanGate.gasSteps_exit input h7

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
