import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreFixed4Tail
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
def gasSteps_csFixed4 (s : State) (memory : ByteArray) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hact : 91 ≤ s.activeWords.toNat)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs : MachineState.readWord memory 2784 = UInt256.ofNat (32 * 4))
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory 4 4).memory 2784 = UInt256.ofNat (32 * 4))
    (hdstFit : pdst.toNat + 32 * 4 ≤ 2912)
    (hsrcFit : (csSrc memory 4 4).toNat + 32 * 4 ≤ 2912) :
    Challenge.EvmProof.GasSteps (subEntryState s memory pdst ret rest)
      (subReturnedState s memory 4 4 pdst ret rest) := by

  have hEntry4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedEntry4
    (by simpa [subEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [subEntryState, State.fork] using hfork)
    (run_csFixedEntry4 s memory pdst ret rest hcap hrun hcode hact hs)
    (by simpa [subEntryState] using hrun)
    (by simpa [subEntryState, State.fork] using hnp)

  have hStep4_0 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_0
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_0 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_1 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_1
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_1 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_2 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_2
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_2 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hStep4_3 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedStep4_3
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedStep4_3 s memory pdst ret rest hcap hrun hcode hact)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  have hTail4 := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csFixedTail4
    (by simpa [csFixedState, Artifact.submissionArtifact] using hcode)
    (by simpa [csFixedState, State.fork] using hfork)
    (run_csFixedTail4 s memory pdst ret rest hcap hrun hcode hact (by decide) (by decide) hjump hs32 hdstFit hsrcFit)
    (by simpa [csFixedState] using hrun)
    (by simpa [csFixedState, State.fork] using hnp)

  exact ((((hEntry4.trans hStep4_0).trans hStep4_1).trans hStep4_2).trans hStep4_3).trans hTail4


end Challenge.Modexp.Submission.Proofs.Fast.Csub
