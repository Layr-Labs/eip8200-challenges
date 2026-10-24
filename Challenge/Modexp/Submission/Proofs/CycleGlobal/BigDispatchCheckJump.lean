import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigDispatchDefs
noncomputable section
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace CycleSubmission.Global.BigDispatch
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode

open EvmSemantics
open EvmSemantics.EVM

set_option linter.unusedSimpArgs false in
theorem run_bigCheckJump (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock bigCheckJumpPath
      (bigComparedState input) = some (bigCheckedState input) := by
  have htrue : UInt256.isTrue 1 := by decide
  have h1 : (1 : UInt256).toNat = 1 := by decide
  have h236 : (219 : UInt256).toNat = 219 := by decide
  have h236Word : (219 : UInt256) = UInt256.ofNat 219 := by decide
  simp (config := { maxSteps := 50000 })
    [bigCheckJumpPath, pushAt, opAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      bigComparedState, bigCheckedState, bigEntryState, Dispatch.wordCheckedState,
      Main.headerState, initialState, UInt256.isTrue, htrue, h1, h236,
      h236Word, jump704,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.succ_ofNat_mod]

end CycleSubmission.Global.BigDispatch
