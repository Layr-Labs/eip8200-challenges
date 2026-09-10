import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.Main

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_headerCheck (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock headerCheckPath
      (headerLoadedState input) = some (headerState input) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1200) (b := 3) (by norm_num : 1200 + 3 < 2 ^ 256)
  have hdest : (1223 : UInt256).toNat = 1223 := by decide
  have hdestWord : (1223 : UInt256) = UInt256.ofNat 1223 := by decide
  simp [headerCheckPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerLoadedState, headerState, initialState, hadd, hdest, hdestWord,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
