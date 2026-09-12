import Challenge.Modexp.Submission.Proofs.Fast.CsubCoreGasAdd
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
def gasSteps_csEntry (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hs32 : MachineState.readWord memory 2784 = UInt256.ofNat (32 * n))
    (hn8 : n ≠ 8) (hn4 : n ≠ 4)
    (hact : 91 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hml : MachineState.readWord memory 2848 = UInt256.ofNat (32 * n - 32))
    (htl : MachineState.readWord memory 2880 = UInt256.ofNat (2080 + 32 * n)) :
    Challenge.EvmProof.GasSteps (subEntryState s memory pdst ret rest)
      (csLoopState s memory n 0 pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka csGenericPath
    (by simpa [subEntryState, Artifact.submissionArtifact] using hcode)
    (by simpa [subEntryState, State.fork] using hfork)
    (run_csEntry s memory n pdst ret rest hcap hrun hcode hs32 hn8 hn4 hact hn hn32 hml htl)
    (by simpa [subEntryState] using hrun)
    (by simpa [subEntryState, State.fork] using hnp)

def gasSteps_csIteration (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat) (hj : j + 1 < n) (hn32 : n ≤ 8) :
    Challenge.EvmProof.GasSteps (csLoopState s memory n j pdst ret rest)
      (csLoopState s memory n (j + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1683
    (by simpa [csLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [csLoopState, State.fork] using hfork)
    (run_csLoopBody s memory n j pdst ret rest hcap hrun hcode hact hj hn32)
    (by simpa [csLoopState] using hrun)
    (by simpa [csLoopState, State.fork] using hnp)

def gasSteps_csLoop (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat) (hn32 : n ≤ 8) :
    Challenge.EvmProof.GasSteps (csLoopState s memory n 0 pdst ret rest)
      (csLoopState s memory n (n - 1) pdst ret rest) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded (n - 1) fun i hi =>
    gasSteps_csIteration s memory n i pdst ret rest hcap hcode hfork hrun hnp hact
      (by omega) hn32

def gasSteps_csExit (s : State) (memory : ByteArray) (n : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8) :
    Challenge.EvmProof.GasSteps (csLoopState s memory n (n - 1) pdst ret rest)
      (csTailState s memory n (n - 1 + 1) pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1683
    (by simpa [csLoopState, Artifact.submissionArtifact] using hcode)
    (by simpa [csLoopState, State.fork] using hfork)
    (run_csLoopExit s memory n (n - 1) pdst ret rest hcap hrun hcode hact
      (by omega) hn32)
    (by simpa [csLoopState] using hrun)
    (by simpa [csLoopState, State.fork] using hnp)

def gasSteps_csTailStep (s : State) (memory : ByteArray) (n j : Nat)
    (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 91 ≤ s.activeWords.toNat) (hn : 2 ≤ n) (hn32 : n ≤ 8)
    (hjump : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode ret.toNat = true)
    (hs32 : MachineState.readWord (csStep memory n j).memory 2784 =
      UInt256.ofNat (32 * n))
    (hdstFit : pdst.toNat + 32 * n ≤ 2912)
    (hsrcFit : (csSrc memory n j).toNat + 32 * n ≤ 2912) :
    Challenge.EvmProof.GasSteps (csTailState s memory n j pdst ret rest)
      (subReturnedState s memory n j pdst ret rest) :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka blk1724
    (by simpa [csTailState, Artifact.submissionArtifact] using hcode)
    (by simpa [csTailState, State.fork] using hfork)
    (run_csTail s memory n j pdst ret rest hcap hrun hcode hact hn hn32 hjump hs32
      hdstFit hsrcFit)
    (by simpa [csTailState] using hrun)
    (by simpa [csTailState, State.fork] using hnp)


end Challenge.Modexp.Submission.Proofs.Fast.Csub
