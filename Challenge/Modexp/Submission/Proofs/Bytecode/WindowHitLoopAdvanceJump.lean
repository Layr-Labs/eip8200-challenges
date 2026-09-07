import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitPaths
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvanceHead

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvanceJump

open EvmSemantics
open EvmSemantics.EVM
open WindowHitPaths

@[simp] private theorem advanceJumpPCs (index : Nat)
    (hlo : 2322 ≤ index) (hhi : index ≤ 2323) :
    Artifact.submissionArtifact.instructionPC index =
      [3551, 3554][index - 2322]! := by
  interval_cases index <;> decide

set_option linter.unusedSimpArgs false in
theorem run (template : State)
    (pointer accumulator modulus : UInt256) (rest : List UInt256)
    (hrest : rest.length ≤ 1000) (hrun : template.halt = .Running)
    (hcode : template.executionEnv.code = submissionBytecode) :
    Challenge.EvmProof.Stepper.runLocatedBlock (loopAdvancePath.drop 3)
      (WindowHitLoopAdvanceHead.framed template 3551
        (pointer :: accumulator :: modulus :: rest)) =
    some (WindowHitLoopAdvanceHead.framed template 3197
      (pointer :: accumulator :: modulus :: rest)) := by
  have hcap3 : rest.length + 3 < 1024 := by omega
  have hcap4 : rest.length + 4 < 1024 := by omega
  simp (disch := omega) [loopAdvancePath, Main.opAt, Main.pushAt, Main.wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, WindowHitLoopAdvanceHead.framed,
    hrun, hcode, advanceJumpPCs, List.getElem?_cons_zero, Option.getD_some,
    Nat.add_assoc, hrest, hcap3, hcap4, jump3197,
    Challenge.EvmProof.Word.literal_eq_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod]

end Challenge.Modexp.Submission.Proofs.Bytecode.WindowHitLoopAdvanceJump
