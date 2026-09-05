import Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatchDefs
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigTailFrame (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigTailFramePath
      (bigCheckedState input) = some (bigTailFrameState input) := by
  have h1283Word : (1289 : UInt256) = UInt256.ofNat 1289 := by decide
  simp (config := { maxSteps := 80000 })
    [bigTailFramePath, opAt, pushAt, wfOp, bigCheckedState,
      Dispatch.wordCheckedState, bigTailFrameState, Main.headerState,
      initialState, Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigTailPCs, h1283Word,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

end Challenge.Modexp.Submission.Proofs.Bytecode.BigDispatch
