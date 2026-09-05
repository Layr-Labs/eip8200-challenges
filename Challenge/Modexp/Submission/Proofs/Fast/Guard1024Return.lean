import Challenge.Modexp.Submission.Proofs.Fast.Guard1024State
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Paths
set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000
namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Return
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024State Guard1024Paths

set_option linter.unusedSimpArgs false in
theorem run_return (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock returnPath (branchState input 4690) =
      some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 }) [returnPath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, returnedState, branchState, initialState,
    answerMemory, storeWord, guardPC2, MachineState.mstore,
    State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Return
