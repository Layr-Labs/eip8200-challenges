import Challenge.Ripemd160.Submission.Proofs.Bytecode.Msize
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardLoop

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

/-- The tail needs only that the accumulator is nonzero.  Stating it that way lets
the 256-byte path, which reaches this tail through the merged classifier, use it. -/
theorem run_tail_fallback_acc (input : ByteArray) (hneAcc : finalAcc input ≠ 0) :
    run tailPath (loopExitState input) = some (fallbackState input) := by
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
  have hdest : Decode.isValidJumpDest submissionBytecode 0x168 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 200 (by rfl)
  simp (config := { maxSteps := 1000000 })
    [tailPath, opAt, pushAt, wfOp, loopExitState, fallbackState, atPC,
    htrue', hdest, List.exchange,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.literal_eq_ofNat, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_tail_fallback (input : ByteArray) (hsize : input.size = 1000)
    (hne : input ≠ KnownInputData.targetInput) :
    run tailPath (loopExitState input) = some (fallbackState input) :=
  run_tail_fallback_acc input (fun hz =>
    hne ((KnownInputCompactLogic.finalAcc_zero_iff_target input hsize).1 hz))

def returnStorePath : List Located :=
  [pushAt 55 20 972889429405991776604892044862621566948497025487,
   pushAt 56 0 0, opAt 57 .MSTORE]

def returnFinishPath : List Located := [pushAt 59 0 0, opAt 60 .RETURN]

def returnStoredState (input : ByteArray) : State :=
  { atPC input 97 with memory := answerMemory, activeWords := UInt256.ofNat 1 }

def returnSizedState (input : ByteArray) : State :=
  { returnStoredState input with pc := UInt256.ofNat 98, stack := [UInt256.ofNat 32] }

theorem run_returnStore (input : ByteArray) :
    run returnStorePath (returnEntry input) = some (returnStoredState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnStorePath, opAt, pushAt, wfOp, returnEntry, atPC, returnStoredState,
    answerMemory, storeWord, ExactGuardSpec.paddedDigestWord,
    MachineState.mstore, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

theorem run_returnFinish (input : ByteArray) :
    run returnFinishPath (returnSizedState input) = some (returnedState input) := by
  have hzeroNat : ({ val := 0 } : UInt256).toNat = 0 := rfl
  simp (config := { maxSteps := 1000000 })
    [returnFinishPath, opAt, pushAt, wfOp, returnSizedState, returnStoredState,
    atPC, returnedState, State.activeWordsAfterUInt256,
    MachineState.activeWordsAfter, hzeroNat,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
    Word.word_toNat_ofNat]

def gasSteps_return :
    GasSteps (returnEntry KnownInputData.targetInput)
      (returnedState KnownInputData.targetInput) := by
  let input := KnownInputData.targetInput
  have gs := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    returnStorePath (by rfl) (by rfl) (run_returnStore input) (by rfl)
    deployAddress_not_precompile
  have hd := Artifact.submissionArtifact.decodeAt_op_index 58 .MSIZE
    (by rfl) (by decide) trivial
  have hp : (returnStoredState input).pc.toNat =
      Artifact.submissionArtifact.instructionPC 58 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have hop : (returnStoredState input).decodedOp = some .MSIZE :=
    Artifact.submissionArtifact.state_decodedOp_of (returnStoredState input) 58
      (by rfl) hp .MSIZE none hd (by rfl)
  have gmraw := Msize.step hop (by simp [returnStoredState, atPC]) (by rfl)
    deployAddress_not_precompile
  have gm : GasSteps (returnStoredState input) (returnSizedState input) := by
    simpa [returnStoredState, returnSizedState, atPC,
      Word.succ_ofNat_mod, Word.word_toNat_ofNat] using gmraw
  have gf := Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    returnFinishPath (by rfl) (by rfl) (run_returnFinish input) (by rfl)
    deployAddress_not_precompile
  exact gs.trans (gm.trans gf)

#print axioms gasSteps_return

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
