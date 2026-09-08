import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanGate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def doneState (input : ByteArray) : State :=
  stS input 5192 [UInt256.ofNat (scalarAt 8), 256, scanAcc input 8, P7, M, m7, P, m8]

def gasSteps_last (input : ByteArray) (hsize : input.size = 256) :
    GasSteps (compareState input 7 (11 + scalarAt 7) (scanAcc input 7))
      (doneState input) := by
  have hfold := gasSteps_compare_fold input (guardWord 7)
    (UInt256.mul M (UInt256.ofNat (scalarAt 7)))
    (UInt256.ofNat (11 + scalarAt 7)) (UInt256.ofNat (32 * 7)) (scanAcc input 7)
  have hexit := gasSteps_size_done input
    (UInt256.land 255 (160 + UInt256.ofNat (11 + scalarAt 7)))
    ((32 : UInt256) + UInt256.ofNat (32 * 7))
    [UInt256.lor (scanAcc input 7)
      (UInt256.xor (MachineState.readWord input (UInt256.ofNat (32 * 7)).toNat)
        (guardWord 7)), P7, M, m7, P, m8]
    (by simp) (by rw [hsize]; rfl)
  have hs := scalar_step (11 + scalarAt 7) 7 (by decide) (by decide)
  have ho := offset_step 7 (by norm_num)
  have hr : (UInt256.ofNat (32 * 7)).toNat = 32 * 7 := by decide
  have h := hfold.trans hexit
  rw [hs, ho, hr] at h
  convert h using 1 <;> rfl

def gasSteps_scan (input : ByteArray) (hsize : input.size = 256)
    (h7 : PatternedScanGate.firstByte input = 7) :
    GasSteps (patternedEntry input) (doneState input) := by
  have last : GasSteps (loopState input 7 (scanAcc input 7)) (doneState input) :=
    (sound wordPath (run_word_straddle input 7 (scanAcc input 7)
      (by norm_num) (by norm_num))).trans
      ((gasSteps_straddle input 7 (scanAcc input 7) (by norm_num)).trans
        (gasSteps_last input hsize))
  exact (PatternedScanGate.gasSteps_pass input h7).trans ((sound setupPath (run_setup input)).trans
    ((gasStep0 input (by rw [hsize]; decide)).trans
      ((gasStep1 input (by rw [hsize]; decide)).trans
        ((gasStep2 input (by rw [hsize]; decide)).trans
          ((gasStep3 input (by rw [hsize]; decide)).trans
            ((gasStep4 input (by rw [hsize]; decide)).trans
              ((gasStep5 input (by rw [hsize]; decide)).trans
                ((gasStep6 input (by rw [hsize]; decide)).trans last))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix256Scan
