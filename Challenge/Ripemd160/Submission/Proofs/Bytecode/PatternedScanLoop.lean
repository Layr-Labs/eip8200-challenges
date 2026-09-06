import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanCompare
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanStraddle

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

/-!
# The thirty-one iterations of the scan

Each iteration derives the expected word from the running scalar, routes the
three straddling offsets through the correction, folds the difference into the
accumulator and advances.  The thirty-first falls through to the padded tail.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedSwar

def gasStep0 (input : ByteArray) :
    GasSteps (loopState input 0 (scanAcc input 0))
      (loopState input 1 (scanAcc input 1)) :=
  ((sound wordPath (run_word_regular input 0 (scanAcc input 0)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 0 (scalarAt 0) (scanAcc input 0)
      (by norm_num) (by decide) (by decide)))

def gasStep1 (input : ByteArray) :
    GasSteps (loopState input 1 (scanAcc input 1))
      (loopState input 2 (scanAcc input 2)) :=
  ((sound wordPath (run_word_regular input 1 (scanAcc input 1)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 1 (scalarAt 1) (scanAcc input 1)
      (by norm_num) (by decide) (by decide)))

def gasStep2 (input : ByteArray) :
    GasSteps (loopState input 2 (scanAcc input 2))
      (loopState input 3 (scanAcc input 3)) :=
  ((sound wordPath (run_word_regular input 2 (scanAcc input 2)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 2 (scalarAt 2) (scanAcc input 2)
      (by norm_num) (by decide) (by decide)))

def gasStep3 (input : ByteArray) :
    GasSteps (loopState input 3 (scanAcc input 3))
      (loopState input 4 (scanAcc input 4)) :=
  ((sound wordPath (run_word_regular input 3 (scanAcc input 3)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 3 (scalarAt 3) (scanAcc input 3)
      (by norm_num) (by decide) (by decide)))

def gasStep4 (input : ByteArray) :
    GasSteps (loopState input 4 (scanAcc input 4))
      (loopState input 5 (scanAcc input 5)) :=
  ((sound wordPath (run_word_regular input 4 (scanAcc input 4)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 4 (scalarAt 4) (scanAcc input 4)
      (by norm_num) (by decide) (by decide)))

def gasStep5 (input : ByteArray) :
    GasSteps (loopState input 5 (scanAcc input 5))
      (loopState input 6 (scanAcc input 6)) :=
  ((sound wordPath (run_word_regular input 5 (scanAcc input 5)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 5 (scalarAt 5) (scanAcc input 5)
      (by norm_num) (by decide) (by decide)))

def gasStep6 (input : ByteArray) :
    GasSteps (loopState input 6 (scanAcc input 6))
      (loopState input 7 (scanAcc input 7)) :=
  ((sound wordPath (run_word_regular input 6 (scanAcc input 6)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 6 (scalarAt 6) (scanAcc input 6)
      (by norm_num) (by decide) (by decide)))

def gasStep7 (input : ByteArray) :
    GasSteps (loopState input 7 (scanAcc input 7))
      (loopState input 8 (scanAcc input 8)) :=
  ((sound wordPath (run_word_straddle input 7 (scanAcc input 7)
      (by norm_num) (by norm_num))).trans
    ((gasSteps_straddle input 7 (scanAcc input 7) (by norm_num)).trans
      (gasSteps_compare_more input 7 (11 + scalarAt 7) (scanAcc input 7)
        (by norm_num) (by decide) (by decide))))

def gasStep8 (input : ByteArray) :
    GasSteps (loopState input 8 (scanAcc input 8))
      (loopState input 9 (scanAcc input 9)) :=
  ((sound wordPath (run_word_regular input 8 (scanAcc input 8)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 8 (scalarAt 8) (scanAcc input 8)
      (by norm_num) (by decide) (by decide)))

def gasStep9 (input : ByteArray) :
    GasSteps (loopState input 9 (scanAcc input 9))
      (loopState input 10 (scanAcc input 10)) :=
  ((sound wordPath (run_word_regular input 9 (scanAcc input 9)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 9 (scalarAt 9) (scanAcc input 9)
      (by norm_num) (by decide) (by decide)))

def gasStep10 (input : ByteArray) :
    GasSteps (loopState input 10 (scanAcc input 10))
      (loopState input 11 (scanAcc input 11)) :=
  ((sound wordPath (run_word_regular input 10 (scanAcc input 10)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 10 (scalarAt 10) (scanAcc input 10)
      (by norm_num) (by decide) (by decide)))

def gasStep11 (input : ByteArray) :
    GasSteps (loopState input 11 (scanAcc input 11))
      (loopState input 12 (scanAcc input 12)) :=
  ((sound wordPath (run_word_regular input 11 (scanAcc input 11)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 11 (scalarAt 11) (scanAcc input 11)
      (by norm_num) (by decide) (by decide)))

def gasStep12 (input : ByteArray) :
    GasSteps (loopState input 12 (scanAcc input 12))
      (loopState input 13 (scanAcc input 13)) :=
  ((sound wordPath (run_word_regular input 12 (scanAcc input 12)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 12 (scalarAt 12) (scanAcc input 12)
      (by norm_num) (by decide) (by decide)))

def gasStep13 (input : ByteArray) :
    GasSteps (loopState input 13 (scanAcc input 13))
      (loopState input 14 (scanAcc input 14)) :=
  ((sound wordPath (run_word_regular input 13 (scanAcc input 13)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 13 (scalarAt 13) (scanAcc input 13)
      (by norm_num) (by decide) (by decide)))

def gasStep14 (input : ByteArray) :
    GasSteps (loopState input 14 (scanAcc input 14))
      (loopState input 15 (scanAcc input 15)) :=
  ((sound wordPath (run_word_regular input 14 (scanAcc input 14)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 14 (scalarAt 14) (scanAcc input 14)
      (by norm_num) (by decide) (by decide)))

def gasStep15 (input : ByteArray) :
    GasSteps (loopState input 15 (scanAcc input 15))
      (loopState input 16 (scanAcc input 16)) :=
  ((sound wordPath (run_word_straddle input 15 (scanAcc input 15)
      (by norm_num) (by norm_num))).trans
    ((gasSteps_straddle input 15 (scanAcc input 15) (by norm_num)).trans
      (gasSteps_compare_more input 15 (11 + scalarAt 15) (scanAcc input 15)
        (by norm_num) (by decide) (by decide))))

def gasStep16 (input : ByteArray) :
    GasSteps (loopState input 16 (scanAcc input 16))
      (loopState input 17 (scanAcc input 17)) :=
  ((sound wordPath (run_word_regular input 16 (scanAcc input 16)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 16 (scalarAt 16) (scanAcc input 16)
      (by norm_num) (by decide) (by decide)))

def gasStep17 (input : ByteArray) :
    GasSteps (loopState input 17 (scanAcc input 17))
      (loopState input 18 (scanAcc input 18)) :=
  ((sound wordPath (run_word_regular input 17 (scanAcc input 17)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 17 (scalarAt 17) (scanAcc input 17)
      (by norm_num) (by decide) (by decide)))

def gasStep18 (input : ByteArray) :
    GasSteps (loopState input 18 (scanAcc input 18))
      (loopState input 19 (scanAcc input 19)) :=
  ((sound wordPath (run_word_regular input 18 (scanAcc input 18)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 18 (scalarAt 18) (scanAcc input 18)
      (by norm_num) (by decide) (by decide)))

def gasStep19 (input : ByteArray) :
    GasSteps (loopState input 19 (scanAcc input 19))
      (loopState input 20 (scanAcc input 20)) :=
  ((sound wordPath (run_word_regular input 19 (scanAcc input 19)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 19 (scalarAt 19) (scanAcc input 19)
      (by norm_num) (by decide) (by decide)))

def gasStep20 (input : ByteArray) :
    GasSteps (loopState input 20 (scanAcc input 20))
      (loopState input 21 (scanAcc input 21)) :=
  ((sound wordPath (run_word_regular input 20 (scanAcc input 20)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 20 (scalarAt 20) (scanAcc input 20)
      (by norm_num) (by decide) (by decide)))

def gasStep21 (input : ByteArray) :
    GasSteps (loopState input 21 (scanAcc input 21))
      (loopState input 22 (scanAcc input 22)) :=
  ((sound wordPath (run_word_regular input 21 (scanAcc input 21)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 21 (scalarAt 21) (scanAcc input 21)
      (by norm_num) (by decide) (by decide)))

def gasStep22 (input : ByteArray) :
    GasSteps (loopState input 22 (scanAcc input 22))
      (loopState input 23 (scanAcc input 23)) :=
  ((sound wordPath (run_word_regular input 22 (scanAcc input 22)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 22 (scalarAt 22) (scanAcc input 22)
      (by norm_num) (by decide) (by decide)))

def gasStep23 (input : ByteArray) :
    GasSteps (loopState input 23 (scanAcc input 23))
      (loopState input 24 (scanAcc input 24)) :=
  ((sound wordPath (run_word_straddle input 23 (scanAcc input 23)
      (by norm_num) (by norm_num))).trans
    ((gasSteps_straddle input 23 (scanAcc input 23) (by norm_num)).trans
      (gasSteps_compare_more input 23 (11 + scalarAt 23) (scanAcc input 23)
        (by norm_num) (by decide) (by decide))))

def gasStep24 (input : ByteArray) :
    GasSteps (loopState input 24 (scanAcc input 24))
      (loopState input 25 (scanAcc input 25)) :=
  ((sound wordPath (run_word_regular input 24 (scanAcc input 24)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 24 (scalarAt 24) (scanAcc input 24)
      (by norm_num) (by decide) (by decide)))

def gasStep25 (input : ByteArray) :
    GasSteps (loopState input 25 (scanAcc input 25))
      (loopState input 26 (scanAcc input 26)) :=
  ((sound wordPath (run_word_regular input 25 (scanAcc input 25)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 25 (scalarAt 25) (scanAcc input 25)
      (by norm_num) (by decide) (by decide)))

def gasStep26 (input : ByteArray) :
    GasSteps (loopState input 26 (scanAcc input 26))
      (loopState input 27 (scanAcc input 27)) :=
  ((sound wordPath (run_word_regular input 26 (scanAcc input 26)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 26 (scalarAt 26) (scanAcc input 26)
      (by norm_num) (by decide) (by decide)))

def gasStep27 (input : ByteArray) :
    GasSteps (loopState input 27 (scanAcc input 27))
      (loopState input 28 (scanAcc input 28)) :=
  ((sound wordPath (run_word_regular input 27 (scanAcc input 27)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 27 (scalarAt 27) (scanAcc input 27)
      (by norm_num) (by decide) (by decide)))

def gasStep28 (input : ByteArray) :
    GasSteps (loopState input 28 (scanAcc input 28))
      (loopState input 29 (scanAcc input 29)) :=
  ((sound wordPath (run_word_regular input 28 (scanAcc input 28)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 28 (scalarAt 28) (scanAcc input 28)
      (by norm_num) (by decide) (by decide)))

def gasStep29 (input : ByteArray) :
    GasSteps (loopState input 29 (scanAcc input 29))
      (loopState input 30 (scanAcc input 30)) :=
  ((sound wordPath (run_word_regular input 29 (scanAcc input 29)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_more input 29 (scalarAt 29) (scanAcc input 29)
      (by norm_num) (by decide) (by decide)))

def gasStep30 (input : ByteArray) :
    GasSteps (loopState input 30 (scanAcc input 30))
      (tailState input (scanAcc input 31)) :=
  ((sound wordPath (run_word_regular input 30 (scanAcc input 30)
      (by norm_num) (by decide))).trans
    (gasSteps_compare_last input (scalarAt 30) (scanAcc input 30)
      (by decide) (by decide)))

/-- The whole scan, from the first word to the padded tail. -/
def gasSteps_scan (input : ByteArray) :
    GasSteps (loopState input 0 0) (tailState input (scanAcc input 31)) :=
  (gasStep0 input).trans ((gasStep1 input).trans ((gasStep2 input).trans ((gasStep3 input).trans ((gasStep4 input).trans ((gasStep5 input).trans ((gasStep6 input).trans ((gasStep7 input).trans ((gasStep8 input).trans ((gasStep9 input).trans ((gasStep10 input).trans ((gasStep11 input).trans ((gasStep12 input).trans ((gasStep13 input).trans ((gasStep14 input).trans ((gasStep15 input).trans ((gasStep16 input).trans ((gasStep17 input).trans ((gasStep18 input).trans ((gasStep19 input).trans ((gasStep20 input).trans ((gasStep21 input).trans ((gasStep22 input).trans ((gasStep23 input).trans ((gasStep24 input).trans ((gasStep25 input).trans ((gasStep26 input).trans ((gasStep27 input).trans ((gasStep28 input).trans ((gasStep29 input).trans (gasStep30 input))))))))))))))))))))))))))))))

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
