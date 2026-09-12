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
  -- The block ends in `POP` rather than `JUMP`, so the last step is a fall-through.
  -- `hdest`/`hdestWord` justified the jump target as a word and are now unreachable -- and this
  -- module sets `warningAsError true`, so an unused `have` is fatal rather than untidy.
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := 1063) (b := 3) (by norm_num : 1063 + 3 < 2 ^ 256)
  simp [headerCheckPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerLoadedState, headerState, initialState, hadd,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
