import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScanLogic
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376InputData

set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLogic

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedScanLogic Patterned376InputData

theorem scanAcc_patterned376 (n : Nat) (hn : n ≤ 376) :
    scanAcc patterned376Input n = 0 := by
  rw [scanAcc_zero_iff patterned376Input n (fun i hi => by
    rw [patterned376Input_size]; omega)]
  intro i hi
  exact patterned376Input_getElem i (by rw [patterned376Input_size]; omega)

theorem scanAcc_zero_iff_eq (input : ByteArray) (hsize : input.size = 376) :
    scanAcc input 376 = 0 ↔ input = patterned376Input := by
  rw [scanAcc_zero_iff input 376 (fun i hi => by rw [hsize]; exact hi)]
  constructor
  · intro hall
    apply ByteArray.ext_getElem
    · exact hsize.trans patterned376Input_size.symm
    · intro i hi hiPattern
      have hi376 : i < 376 := by simpa [hsize] using hi
      exact (hall i hi376).trans (patterned376Input_getElem i hiPattern).symm
  · rintro rfl i hi
    exact patterned376Input_getElem i (by rw [patterned376Input_size]; exact hi)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Patterned376ScanLogic
