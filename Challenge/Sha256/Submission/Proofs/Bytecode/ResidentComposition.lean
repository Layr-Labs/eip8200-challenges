import Challenge.Sha256.Submission.Proofs.Bytecode.ResidentSegment

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000

namespace Challenge.Sha256.Submission.Proofs.Bytecode.ResidentComposition

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Sha256.Submission.Proofs.Bytecode

def gasStepsPair (base ghost : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (j : Nat) (hj : j + 2 ≤ 64)
    (hcap : rest.length < 988)
    (hcode : base.executionEnv.code = submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false)
    (hW0 : MachineState.readWord base.memory (Compression.pairWPtr j).toNat =
      Compression.wValue ghost j)
    (hK0 : UInt256.ofNat 0xffffffff &&&
        MachineState.readWord base.memory (Compression.pairKPtr j).toNat =
      Compression.kValue ghost j)
    (hW1 : MachineState.readWord base.memory
        (UInt256.ofNat 32 + Compression.pairWPtr j).toNat =
      Compression.wValue ghost (j + 1))
    (hK1 : UInt256.land (UInt256.ofNat 0xffffffff)
        (MachineState.readWord base.memory
          (UInt256.ofNat 4 + Compression.pairKPtr j).toNat) =
      Compression.kValue ghost (j + 1)) :
    Challenge.EvmProof.GasSteps
      (Compression.residentAt base ghost msgOff returnDest rest j)
      (Compression.residentAfterPair base ghost msgOff returnDest rest j) := by
  have hj64 : j < 64 := by omega
  have gCond : Challenge.EvmProof.GasSteps
      (Compression.residentAt base ghost msgOff returnDest rest j)
      (Compression.residentAfterCondition base ghost msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairConditionPath
    · exact hcode
    · exact hfork
    · exact Compression.run_pairCondition base ghost msgOff returnDest rest j hj64
        (by omega) hrun
    · exact hrun
    · exact hnp
  have gSetup10 : Challenge.EvmProof.GasSteps
      (Compression.residentAfterCondition base ghost msgOff returnDest rest j)
      (Compression.residentCallT10 base ghost msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairFirstSetupPath
    · exact hcode
    · exact hfork
    · exact ResidentSegment.runFirstSetup base ghost msgOff returnDest rest j
        (by omega) hcode hrun hW0 hK0
    · exact hrun
    · exact hnp
  have valid708 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 708).toNat = true := by
    decide
  have gT10 : Challenge.EvmProof.GasSteps
      (Compression.residentCallT10 base ghost msgOff returnDest rest j)
      (Compression.residentAfterT10 base ghost msgOff returnDest rest j) := by
    simpa [Compression.residentCallT10, Compression.residentAfterT10] using
      (BigSigma.gasSteps_bigSigma1
        (Compression.residentFirstInputsLoaded base ghost msgOff returnDest rest j)
        (Compression.hValue ghost 4) (Compression.hValue ghost 5)
        (Compression.hValue ghost 6)
        (Compression.hValue ghost 7 + Compression.kValue ghost j)
        (Compression.wValue ghost j) (UInt256.ofNat 708)
        ([Compression.kValue ghost j, Compression.wValue ghost j,
          Compression.hValue ghost 0, Compression.hValue ghost 4,
          Compression.hValue ghost 5, Compression.hValue ghost 6,
          Compression.hValue ghost 7, Compression.hValue ghost 1,
          Compression.hValue ghost 2, Compression.hValue ghost 3,
          Compression.pairWPtr j, Compression.pairKPtr j,
          msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid708)
  have gSetup20 : Challenge.EvmProof.GasSteps
      (Compression.residentAfterT10 base ghost msgOff returnDest rest j)
      (Compression.residentCallT20 base ghost msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairFirstT2SetupPath
    · exact hcode
    · exact hfork
    · exact ResidentSegment.runFirstT2Setup base ghost msgOff returnDest rest j
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have valid728 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 728).toNat = true := by
    decide
  have gT20 : Challenge.EvmProof.GasSteps
      (Compression.residentCallT20 base ghost msgOff returnDest rest j)
      (Compression.residentAfterT20 base ghost msgOff returnDest rest j) := by
    simpa [Compression.residentCallT20, Compression.residentAfterT20] using
      (BigSigma.gasSteps_bigSigma0
        (Compression.residentAfterT10 base ghost msgOff returnDest rest j)
        (Compression.hValue ghost 0) (Compression.hValue ghost 1)
        (Compression.hValue ghost 2) (UInt256.ofNat 728)
        ([Compression.t10 ghost j, Compression.hValue ghost 0,
          Compression.hValue ghost 4, Compression.hValue ghost 5,
          Compression.hValue ghost 6, Compression.hValue ghost 7,
          Compression.hValue ghost 1, Compression.hValue ghost 2,
          Compression.hValue ghost 3, Compression.pairWPtr j,
          Compression.pairKPtr j, msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid728)
  have gSetup11 : Challenge.EvmProof.GasSteps
      (Compression.residentAfterT20 base ghost msgOff returnDest rest j)
      (Compression.residentCallT11 base ghost msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairSecondT1SetupPath
    · exact hcode
    · exact hfork
    · exact ResidentSegment.runSecondT1Setup base ghost msgOff returnDest rest j
        (by omega) hcode hrun hW1 hK1
    · exact hrun
    · exact hnp
  have valid783 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 783).toNat = true := by
    decide
  have gT11 : Challenge.EvmProof.GasSteps
      (Compression.residentCallT11 base ghost msgOff returnDest rest j)
      (Compression.residentAfterT11 base ghost msgOff returnDest rest j) := by
    simpa [Compression.residentCallT11, Compression.residentAfterT11] using
      (BigSigma.gasSteps_bigSigma1
        (Compression.residentSecondInputsLoaded base ghost msgOff returnDest rest j)
        (Compression.pairE1 ghost j) (Compression.hValue ghost 4)
        (Compression.hValue ghost 5)
        (Compression.hValue ghost 6 + Compression.kValue ghost (j + 1))
        (Compression.wValue ghost (j + 1)) (UInt256.ofNat 783)
        ([Compression.kValue ghost (j + 1), Compression.wValue ghost (j + 1),
          Compression.pairA1 ghost j, Compression.pairE1 ghost j,
          Compression.hValue ghost 0, Compression.hValue ghost 4,
          Compression.hValue ghost 5, Compression.hValue ghost 6,
          Compression.hValue ghost 7, Compression.hValue ghost 1,
          Compression.hValue ghost 2, Compression.hValue ghost 3,
          Compression.pairWPtr j, Compression.pairKPtr j,
          msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid783)
  have gSetup21 : Challenge.EvmProof.GasSteps
      (Compression.residentAfterT11 base ghost msgOff returnDest rest j)
      (Compression.residentCallT21 base ghost msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairSecondT2SetupPath
    · exact hcode
    · exact hfork
    · exact ResidentSegment.runSecondT2Setup base ghost msgOff returnDest rest j
        (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have valid803 :
      Decode.isValidJumpDest submissionBytecode (UInt256.ofNat 803).toNat = true := by
    decide
  have gT21 : Challenge.EvmProof.GasSteps
      (Compression.residentCallT21 base ghost msgOff returnDest rest j)
      (Compression.residentAfterT21 base ghost msgOff returnDest rest j) := by
    simpa [Compression.residentCallT21, Compression.residentAfterT21] using
      (BigSigma.gasSteps_bigSigma0
        (Compression.residentAfterT11 base ghost msgOff returnDest rest j)
        (Compression.pairA1 ghost j) (Compression.hValue ghost 0)
        (Compression.hValue ghost 1) (UInt256.ofNat 803)
        ([Compression.t11 ghost j, Compression.pairA1 ghost j,
          Compression.pairE1 ghost j, Compression.hValue ghost 0,
          Compression.hValue ghost 4, Compression.hValue ghost 5,
          Compression.hValue ghost 6, Compression.hValue ghost 7,
          Compression.hValue ghost 1, Compression.hValue ghost 2,
          Compression.hValue ghost 3, Compression.pairWPtr j,
          Compression.pairKPtr j, msgOff, returnDest] ++ rest)
        (by simp; omega) hcode hfork hrun hnp valid803)
  have gCommit : Challenge.EvmProof.GasSteps
      (Compression.residentAfterT21 base ghost msgOff returnDest rest j)
      (Compression.residentAfterPair base ghost msgOff returnDest rest j) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka Compression.pairCommitPath
    · exact hcode
    · exact hfork
    · exact ResidentSegment.runCommit base ghost msgOff returnDest rest j
        (by omega) (by omega) hcode hrun
    · exact hrun
    · exact hnp
  exact gCond.trans (gSetup10.trans (gT10.trans (gSetup20.trans
    (gT20.trans (gSetup11.trans (gT11.trans (gSetup21.trans
      (gT21.trans gCommit))))))))

end Challenge.Sha256.Submission.Proofs.Bytecode.ResidentComposition
