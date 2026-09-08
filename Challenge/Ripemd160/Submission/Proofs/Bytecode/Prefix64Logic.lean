import Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Data
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Logic

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedScan PatternedSwar

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 64) :
    scanAcc input 2 = 0 ↔ input = Prefix64Data.data := by
  rw [scanAcc_zero_iff]
  constructor
  · intro hw
    apply Prefix64Data.eq_data_of_words input hsize
    intro j hj
    rw [hw j hj, guardWord_eq j (by omega)]
  · rintro rfl j hj
    rw [Prefix64Data.readWord_data j hj, guardWord_eq j (by omega)]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Prefix64Logic
