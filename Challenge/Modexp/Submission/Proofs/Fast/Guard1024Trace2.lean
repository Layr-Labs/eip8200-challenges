import Challenge.Modexp.Submission.Proofs.Fast.Guard1024State
import Challenge.Modexp.Submission.Proofs.Fast.Guard1024Paths

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace2

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode
open Guard1024Logic Guard1024State Guard1024Paths

set_option linter.unusedSimpArgs false in
theorem run_check2 (input : ByteArray) :
    Challenge.EvmProof.Stepper.runLocatedBlock check2Path (accState input 4525 (acc2 input)) =
      some (accState input 4681 (acc3 input)) := by
  have hzeroWord : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp [check2Path, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    accState, acc3, Guard1024State.chunk2, scanDiff, Guard1024Data.checks, initialState, guard1024PC2,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, hzeroWord, hzeroNat]

end Challenge.Modexp.Submission.Proofs.Fast.Guard1024Trace2
