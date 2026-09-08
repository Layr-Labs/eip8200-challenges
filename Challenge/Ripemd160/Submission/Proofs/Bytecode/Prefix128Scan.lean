import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLoop

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Scan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

def doneState (input : ByteArray) : State :=
  stS input 5274 [UInt256.ofNat (scalarAt 4), 128, scanAcc input 4, P7, M, m7, P, m8]

def gasSteps_last (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (compareState input 3 (scalarAt 3) (scanAcc input 3))
      (doneState input) := by
  have hfold := gasSteps_compare_fold input (guardWord 3)
    (UInt256.mul M (UInt256.ofNat (scalarAt 3)))
    (UInt256.ofNat (scalarAt 3)) (UInt256.ofNat (32 * 3)) (scanAcc input 3)
  have hexit := gasSteps_size_done input
    (UInt256.land 255 (160 + UInt256.ofNat (scalarAt 3)))
    ((32 : UInt256) + UInt256.ofNat (32 * 3))
    [UInt256.lor (scanAcc input 3)
      (UInt256.xor (MachineState.readWord input (UInt256.ofNat (32 * 3)).toNat)
        (guardWord 3)), P7, M, m7, P, m8]
    (by simp) (by rw [hsize]; rfl)
  have hs := scalar_step (scalarAt 3) 3 (by decide) (by decide)
  have ho := offset_step 3 (by norm_num)
  have hr : (UInt256.ofNat (32 * 3)).toNat = 32 * 3 := by decide
  have h := hfold.trans hexit
  rw [hs, ho, hr] at h
  convert h using 1 <;> rfl

def gasSteps_scan (input : ByteArray) (hsize : input.size = 128) :
    GasSteps (patternedEntry input) (doneState input) := by
  have last : GasSteps (loopState input 3 (scanAcc input 3)) (doneState input) :=
    (sound wordPath (run_word_regular input 3 (scanAcc input 3)
      (by norm_num) (by decide))).trans (gasSteps_last input hsize)
  exact (sound setupPath (run_setup input)).trans
    ((gasStep0 input (by rw [hsize]; decide)).trans
      ((gasStep1 input (by rw [hsize]; decide)).trans
        ((gasStep2 input (by rw [hsize]; decide)).trans last)))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix128Scan
