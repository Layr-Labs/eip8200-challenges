import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardSize

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! The seed accumulator: reference word and tail word. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open KnownInputCompactState

private def sS (l : Located) {s t : State}
    (h : Challenge.EvmProof.DataStepper.runLocatedBlock [l] s = some t)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code := by rfl)
    (hfork : s.fork = .Osaka := by rfl)
    (hrun : s.halt = .Running := by rfl)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false := by
        exact deployAddress_not_precompile) : GasSteps s t :=
  Challenge.EvmProof.DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    [l] hcode hfork h hrun hnp

/-- The straight-line seed block from PC 33 and the `PUSH1 210 JUMP` at 45 to the loop head at PC 210. -/
def gasSteps_checkEntry (input : ByteArray) :
    GasSteps (sizeMatched input) (loopState input 0) := by
  apply Challenge.EvmProof.DataStepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka
    (checkEntryPath ++ [pushAt 27 1 210, opAt 28 .JUMP])
    (by rfl) (by rfl) _ (by rfl) deployAddress_not_precompile
  have hz : MachineState.readWord ByteArray.empty 0 = UInt256.ofNat 0 := by
    unfold MachineState.readWord
    rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList,
      YulEvmCompiler.ByteArray.toList_eq_data]
    decide
  have p21 : Artifact.submissionArtifact.instructionPC 21 = 35 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have p27 : Artifact.submissionArtifact.instructionPC 27 = 45 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  have p28 : Artifact.submissionArtifact.instructionPC 28 = 47 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; rfl
  simp (config := { maxSteps := 1000000 })
    [checkEntryPath, pushAt, opAt, wfOp, sizeMatched, atPC, loopState,
      initialState, equalityAcc, referenceWord,
      Challenge.EvmProof.DataStepper.runLocatedBlock,
      Challenge.EvmProof.DataStepper.runLocated,
      Challenge.EvmProof.DataStepper.runInstr,
      p21, p27, p28, hz,
      Artifact.validJumpDest_212,
      State.activeWordsAfterUInt256, MachineState.activeWordsAfter,
      Word.literal_eq_ofNat, Word.succ_ofNat_mod, Word.ofNat_add_mod,
      Word.word_toNat_ofNat]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
