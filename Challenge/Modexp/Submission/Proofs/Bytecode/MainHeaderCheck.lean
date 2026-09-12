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
  -- The block is now two `JUMPDEST` fillers where it held `PUSH2 1067; POP`.  Both are stack
  -- no-ops and both advance the pc by one byte, so EVERY step is a `succ` and the `+3` helper that
  -- justified the old `PUSH2`'s stride is unreachable.  It is DELETED rather than left: this
  -- module sets `warningAsError true`, under which an unused `have` is fatal, not untidy -- the
  -- same trap `hdest`/`hdestWord` set on the previous ticket.
  simp [headerCheckPath, opAt, pushAt,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    headerLoadedState, headerState, initialState,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Bytecode.Main
