import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardLoop
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The final word, the two exits and the stored answer. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

theorem shiftRight_xor_192 (a b : UInt256) :
    UInt256.shiftRight (UInt256.xor a b) (UInt256.ofNat 192) =
      UInt256.xor
        (UInt256.shiftRight a (UInt256.ofNat 192))
        (UInt256.shiftRight b (UInt256.ofNat 192)) := by
  unfold UInt256.shiftRight
  have h : ¬ (UInt256.ofNat 192).toNat ≥ 256 := by decide
  rw [if_neg h, if_neg h, if_neg h]
  unfold UInt256.xor
  congr 1
  apply Fin.ext
  change (Fin.shiftRight (Fin.xor a.val b.val) (UInt256.ofNat 192).val).val =
    (Fin.xor
      (Fin.shiftRight a.val (UInt256.ofNat 192).val)
      (Fin.shiftRight b.val (UInt256.ofNat 192).val)).val
  simp only [Fin.shiftRight, Fin.xor]
  have hs : (UInt256.ofNat 192).val.val = 192 := by decide
  rw [hs]
  change (((a.val.val ^^^ b.val.val) % UInt256.size) >>> 192) % UInt256.size =
    (((a.val.val >>> 192) % UInt256.size) ^^^
      ((b.val.val >>> 192) % UInt256.size)) % UInt256.size
  have hab : a.val.val ^^^ b.val.val < UInt256.size :=
    Nat.xor_lt_two_pow a.val.isLt b.val.isLt
  have ha : a.val.val >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) a.val.isLt
  have hb : b.val.val >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) b.val.isLt
  have habs : (a.val.val ^^^ b.val.val) >>> 192 < UInt256.size :=
    Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) hab
  have hshifts : (a.val.val >>> 192) ^^^ (b.val.val >>> 192) < UInt256.size :=
    Nat.xor_lt_two_pow ha hb
  rw [Nat.mod_eq_of_lt hab, Nat.mod_eq_of_lt habs,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hshifts]
  exact Nat.shiftRight_xor_distrib

theorem run_tail_target :
    run tailPath (loopExitState KnownInputData.targetInput) =
      some (returnEntry KnownInputData.targetInput) := by
  have hzero : finalAcc KnownInputData.targetInput = 0 :=
    (KnownInputCompactLogic.finalAcc_zero_iff_target KnownInputData.targetInput
      KnownInputData.targetInput_size).2 rfl
  have hzero' : UInt256.lor
      (UInt256.shiftRight
        (UInt256.xor (referenceWord KnownInputData.targetInput)
          (MachineState.readWord KnownInputData.targetInput 992))
        (UInt256.ofNat 192))
      (loopAcc KnownInputData.targetInput 30) = 0 := by
    rw [shiftRight_xor_192]
    have hcomm : UInt256.xor
        (UInt256.shiftRight (referenceWord KnownInputData.targetInput) (UInt256.ofNat 192))
        (UInt256.shiftRight (MachineState.readWord KnownInputData.targetInput 992)
          (UInt256.ofNat 192)) =
        UInt256.xor
          (UInt256.shiftRight (MachineState.readWord KnownInputData.targetInput 992)
            (UInt256.ofNat 192))
          (UInt256.shiftRight (referenceWord KnownInputData.targetInput)
            (UInt256.ofNat 192)) := BooleanSelect.xor_comm _ _
    rw [hcomm]
    exact hzero
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, returnEntry, atPC,
    hzero', List.exchange, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_fallback (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ KnownInputData.targetInput) :
    run tailPath (loopExitState input) = some (fallbackState input) := by
  have hneAcc : finalAcc input ≠ 0 := by
    intro hz
    exact hne ((KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1 hz)
  have htrue : UInt256.isTrue (finalAcc input) := by
    intro hz
    apply hneAcc
    apply Challenge.EvmProof.Word.word_ext
    simpa using hz
  have htrue' : UInt256.isTrue
      (UInt256.lor
        (UInt256.shiftRight
          (UInt256.xor (referenceWord input) (MachineState.readWord input 992))
          (UInt256.ofNat 192))
        (loopAcc input 30)) := by
    rw [shiftRight_xor_192]
    have hcomm : UInt256.xor
        (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192))
        (UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192)) =
        UInt256.xor
          (UInt256.shiftRight (MachineState.readWord input 992) (UInt256.ofNat 192))
          (UInt256.shiftRight (referenceWord input) (UInt256.ofNat 192)) :=
      BooleanSelect.xor_comm _ _
    rw [hcomm]
    exact htrue
  have hdest : Decode.isValidJumpDest submissionBytecode 0x3 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 2 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, fallbackState, atPC,
    htrue', hdest, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def returnStored (input : ByteArray) : State :=
  { initialState submissionBytecode input 0 with
    pc := UInt256.ofNat 271
    memory := answerMemory
    activeWords := UInt256.ofNat 1 }

def returnSized (input : ByteArray) : State :=
  { returnStored input with
    pc := UInt256.ofNat 272
    stack := [UInt256.ofNat 32] }

theorem run_return_store :
    run (returnPath.take 3) (returnEntry KnownInputData.targetInput) =
      some (returnStored KnownInputData.targetInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, returnEntry, atPC, returnStored,
    answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_return_finish :
    run (returnPath.drop 4) (returnSized KnownInputData.targetInput) =
      some (returnedState KnownInputData.targetInput) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnPath, opAt, pushAt, wfOp, returnSized, returnStored, returnedState,
    State.activeWordsAfterUInt256, MachineState.activeWordsAfter, hzeroNat,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

def gasSteps_return :
    GasSteps (returnEntry KnownInputData.targetInput)
      (returnedState KnownInputData.targetInput) := by
  have gs := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (returnPath.take 3)
    (by rfl) (by rfl) run_return_store (by rfl) deployAddress_not_precompile
  have hd := Artifact.submissionArtifact.decodeAt_op_index
    158 .MSIZE (by rfl) (by decide) trivial
  have hp : (returnStored KnownInputData.targetInput).pc.toNat =
      Artifact.submissionArtifact.instructionPC 158 := by
    rw [pc2857]
    rfl
  have hop : (returnStored KnownInputData.targetInput).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of
      (returnStored KnownInputData.targetInput) 158 (by rfl) hp .MSIZE none hd (by decide)
  have gmraw := Msize.step hop (by simp [returnStored]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (returnStored KnownInputData.targetInput)
      (returnSized KnownInputData.targetInput) := by
    simpa [returnStored, returnSized,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat] using gmraw
  have gr := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka (returnPath.drop 4)
    (by rfl) (by rfl) run_return_finish (by rfl) deployAddress_not_precompile
  exact gs.trans (gm.trans gr)

#print axioms gasSteps_return

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
