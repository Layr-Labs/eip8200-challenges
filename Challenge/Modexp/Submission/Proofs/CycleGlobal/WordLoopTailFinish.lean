import Challenge.Modexp.Submission.Proofs.CycleGlobal.PCCertificate
import Challenge.Modexp.Submission.Proofs.CycleGlobal.Binding
import Challenge.Modexp.Submission.Proofs.Bytecode.PCFast
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WordLoopTailHead
noncomputable section
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 1000000
namespace CycleSubmission.Global.WordLoops
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Bytecode
open EvmSemantics
open EvmSemantics.EVM
open Word
attribute [local simp] Challenge.EvmProof.Word.ofNat_add_mod
  Challenge.EvmProof.Word.succ_ofNat_mod
@[simp] private theorem exitPCs (i : Nat) (hi : 6347 ≤ i) (hii : i ≤ 6354) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([8433,8434,8435,8436,8437,8439,8440,8442] : List Nat)[i - 6347]! := by
  interval_cases i <;>
    exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
@[simp] private theorem exitPCs_part1 (i : Nat) (hi : 8203 ≤ i) (hii : i ≤ 8216) :
    CycleSubmission.Artifact.artifact.instructionPC i =
      ([10885,10886,10887,10888,10889,10891,10892,10894,10895,10896,10897,10898,10899,10900] : List Nat)[i - 8203]! := by
  interval_cases i <;>
    exact CycleSubmission.PCCertificate.selectedPC _ (by decide)
@[simp] private theorem jump589 :
    Decode.isValidJumpDest CycleSubmission.Artifact.bytecode 152 = true :=
  CycleSubmission.Global.Binding.jumpDest 115 (by rfl)
set_option linter.unusedSimpArgs false in
theorem run_bitFinishTailFinish (input : ByteArray) (outer : Nat)
    (acc base : UInt256) (hvalid : ValidInput input)
    (houter : outer < exponentSize input) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitFinishTailFinishPath
      (bitFinishTailMidState input outer acc base) =
        some (expLoopState input (outer + 1) acc base) := by
  rcases hvalid with ⟨_,hb,he,hm⟩
  have hsucc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := outer) (b := 1) (by omega : outer + 1 < 2 ^ 256)
  have hincLeft : UInt256.ofNat 1 + UInt256.ofNat outer =
      UInt256.ofNat (outer + 1) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hsucc
  have honeWord : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h589 : (152 : UInt256).toNat = 152 := by decide
  have h589Word : (152 : UInt256) = UInt256.ofNat 152 := by decide
  simp (config := { maxSteps := 125000 })
    [bitFinishTailFinishPath,Word.opAt,Word.pushAt,Word.wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated,Challenge.EvmProof.Stepper.runInstr,
      bitFinishTailMidState,bitLoopState,bitTail,expLoopState,nonzeroState,
      callerRest,Dispatch.wordEntryState,Main.headerState,initialState,
      exitPCs,Challenge.EvmProof.Word.word_toNat_ofNat,
      hsucc,hincLeft,honeWord,h589,h589Word,jump589]
end CycleSubmission.Global.WordLoops
