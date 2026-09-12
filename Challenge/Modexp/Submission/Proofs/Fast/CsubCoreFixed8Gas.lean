import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreFixed8Tail
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Csub

attribute [local simp]
  CompactConstants.notThirtyOne CompactConstants.not1087

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs
open Challenge.Modexp.Submission.Proofs.Fast
attribute [local simp] jumpDestCopyResume
attribute [local irreducible] csStep
def gasSteps_csFixed8 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs : MachineState.readWord memory 2784 = UInt256.ofNat (32 * 8))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 8 8).memory 2784 = UInt256.ofNat (32 * 8))
    (hdstFit : pdst.toNat + 32 * 8 ≤ 2912)
    (hsrcFit : (csSrc memory 8 8).toNat + 32 * 8 ≤ 2912) :
    Challenge.EvmProof.GasSteps (subEntryState s memory pdst ret rest)
      (subReturnedState s memory 8 8 pdst ret rest) := by

  have hEntry8 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedEntry8
    (by simpa [subEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [subEntryState, State.fork] using hfork)
    (run_csFixedEntry8 s memory pdst ret rest hcap hrun hcode hact hs)
    (by simpa [subEntryState] using hrun)
    (by simpa [subEntryState, State.fork] using hnp)

  have hStep8_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_0
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_0 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_1
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_1 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_2
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_2 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_3
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_3 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_4
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_4 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_5 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_5
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_5 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_6 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_6
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_6 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep8_7 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep8_7
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep8_7 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hTail8 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedTail8
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedTail8 s memory pdst ret rest hcap hrun hcode hact (by decide) (by decide) hjump hs32 hdstFit hsrcFit)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  exact ((((((((hEntry8.trans hStep8_0).trans hStep8_1).trans hStep8_2).trans hStep8_3).trans hStep8_4).trans hStep8_5).trans hStep8_6).trans hStep8_7).trans hTail8


end Challenge.Modexp.Submission.Proofs.Fast.Csub
