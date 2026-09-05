import Challenge.Modexp.Submission.Proofs.Fast.Guard257State
import Challenge.Modexp.Submission.Proofs.Fast.Guard257Paths
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard257Return
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard257State Guard257Paths

set_option linter.unusedSimpArgs false in
theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (branchState input 4906) =
      some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [returnPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, returnedState, branchState, initialState,
    answerMemory, storeWord, g257PC0, g257PC1, g257PC2, MachineState.mstore,
    State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.Guard257Return
