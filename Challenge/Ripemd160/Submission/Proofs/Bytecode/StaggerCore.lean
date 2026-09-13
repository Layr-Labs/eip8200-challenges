import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCorePairedAll
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCoreBoundaryAll
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Paired144WordRound StaggerCoreCommon StaggerCoreModel
open StaggerModeSeven (physicalKey)
open StaggerModeSeven (step fold)
def pcs : Array Nat := #[1269, 1335, 1377, 1412, 1455, 1493, 1535, 1573, 1615, 1653, 1695, 1733, 1776, 1814, 1884, 1930, 1977, 2041, 2087, 2126, 2173, 2213, 2260, 2300, 2345, 2385, 2429, 2469, 2516, 2553, 2623, 2667, 2712, 2771, 2811, 2843, 2879, 2912, 2950, 2983, 3024, 3054, 3093, 3125, 3162, 3194, 3265, 3312, 3356, 3421, 3466, 3506, 3554, 3593, 3641, 3681, 3728, 3767, 3814, 3853, 3901, 3940, 3991, 4031, 4071, 4116, 4159, 4197, 4240, 4277, 4315, 4350, 4392, 4429, 4472, 4510, 4551, 4587]
def shapes : Array (List Reg) := #[
  [ .pair, .upper, .e, .b, .a, .d, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .a, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .k, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .k, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .k, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .a, .e, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .e, .a, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .a, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .e, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .a, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .b, .k, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .c, .k, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .c, .a, .e, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .k, .b, .e, .a, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .a, .b, .e, .k, .c, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ],
  [ .d, .literal 28, .cachedMessage 360, .pair, .upper, .e, .c, .a, .k, .b, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ]]
def atRound (s : State) (h4 : UInt256) (i : Nat) (q right : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat pcs[i]!, stack := stack s.memory h4 shapes[i]! q right (physicalKey (i-1)) rho}

private def gasSteps_at0 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 0 q right rho)
      (atRound s h4 (0+1) (step 0 (message s.memory 0) q) right rho) := by
  exact StaggerCorePaired0.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at1 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 1 q right rho)
      (atRound s h4 (1+1) (step 1 (message s.memory 1) q) right rho) := by
  exact StaggerCorePaired1.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at2 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 2 q right rho)
      (atRound s h4 (2+1) (step 2 (message s.memory 2) q) right rho) := by
  exact StaggerCorePaired2.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at3 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 3 q right rho)
      (atRound s h4 (3+1) (step 3 (message s.memory 3) q) right rho) := by
  exact StaggerCorePaired3.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at4 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 4 q right rho)
      (atRound s h4 (4+1) (step 4 (message s.memory 4) q) right rho) := by
  exact StaggerCorePaired4.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at5 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 5 q right rho)
      (atRound s h4 (5+1) (step 5 (message s.memory 5) q) right rho) := by
  exact StaggerCorePaired5.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at6 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 6 q right rho)
      (atRound s h4 (6+1) (step 6 (message s.memory 6) q) right rho) := by
  exact StaggerCorePaired6.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at7 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 7 q right rho)
      (atRound s h4 (7+1) (step 7 (message s.memory 7) q) right rho) := by
  exact StaggerCorePaired7.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at8 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 8 q right rho)
      (atRound s h4 (8+1) (step 8 (message s.memory 8) q) right rho) := by
  exact StaggerCorePaired8.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at9 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 9 q right rho)
      (atRound s h4 (9+1) (step 9 (message s.memory 9) q) right rho) := by
  exact StaggerCorePaired9.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at10 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 10 q right rho)
      (atRound s h4 (10+1) (step 10 (message s.memory 10) q) right rho) := by
  exact StaggerCorePaired10.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at11 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 11 q right rho)
      (atRound s h4 (11+1) (step 11 (message s.memory 11) q) right rho) := by
  exact StaggerCorePaired11.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at12 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 12 q right rho)
      (atRound s h4 (12+1) (step 12 (message s.memory 12) q) right rho) := by
  exact StaggerCorePaired12.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at13 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 13 q right rho)
      (atRound s h4 (13+1) (step 13 (message s.memory 13) q) right rho) := by
  exact StaggerCorePaired13.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at14 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 14 q right rho)
      (atRound s h4 (14+1) (step 14 (message s.memory 14) q) right rho) := by
  exact StaggerCorePaired14.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at15 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 15 q right rho)
      (atRound s h4 (15+1) (step 15 (message s.memory 15) q) right rho) := by
  exact StaggerCorePaired15.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at16 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 16 q right rho)
      (atRound s h4 (16+1) (step 16 (message s.memory 16) q) right rho) := by
  exact StaggerCorePaired16.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at17 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 17 q right rho)
      (atRound s h4 (17+1) (step 17 (message s.memory 17) q) right rho) := by
  exact StaggerCorePaired17.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at18 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 18 q right rho)
      (atRound s h4 (18+1) (step 18 (message s.memory 18) q) right rho) := by
  exact StaggerCorePaired18.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at19 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 19 q right rho)
      (atRound s h4 (19+1) (step 19 (message s.memory 19) q) right rho) := by
  exact StaggerCorePaired19.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at20 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 20 q right rho)
      (atRound s h4 (20+1) (step 20 (message s.memory 20) q) right rho) := by
  exact StaggerCorePaired20.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at21 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 21 q right rho)
      (atRound s h4 (21+1) (step 21 (message s.memory 21) q) right rho) := by
  exact StaggerCorePaired21.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at22 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 22 q right rho)
      (atRound s h4 (22+1) (step 22 (message s.memory 22) q) right rho) := by
  exact StaggerCorePaired22.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at23 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 23 q right rho)
      (atRound s h4 (23+1) (step 23 (message s.memory 23) q) right rho) := by
  exact StaggerCorePaired23.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at24 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 24 q right rho)
      (atRound s h4 (24+1) (step 24 (message s.memory 24) q) right rho) := by
  exact StaggerCorePaired24.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at25 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 25 q right rho)
      (atRound s h4 (25+1) (step 25 (message s.memory 25) q) right rho) := by
  exact StaggerCorePaired25.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at26 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 26 q right rho)
      (atRound s h4 (26+1) (step 26 (message s.memory 26) q) right rho) := by
  exact StaggerCorePaired26.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at27 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 27 q right rho)
      (atRound s h4 (27+1) (step 27 (message s.memory 27) q) right rho) := by
  exact StaggerCorePaired27.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at28 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 28 q right rho)
      (atRound s h4 (28+1) (step 28 (message s.memory 28) q) right rho) := by
  exact StaggerCorePaired28.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at29 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 29 q right rho)
      (atRound s h4 (29+1) (step 29 (message s.memory 29) q) right rho) := by
  exact StaggerCorePaired29.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at30 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 30 q right rho)
      (atRound s h4 (30+1) (step 30 (message s.memory 30) q) right rho) := by
  exact StaggerCorePaired30.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at31 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 31 q right rho)
      (atRound s h4 (31+1) (step 31 (message s.memory 31) q) right rho) := by
  exact StaggerCorePaired31.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at32 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 32 q right rho)
      (atRound s h4 (32+1) (step 32 (message s.memory 32) q) right rho) := by
  exact StaggerCorePaired32.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at33 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 33 q right rho)
      (atRound s h4 (33+1) (step 33 (message s.memory 33) q) right rho) := by
  exact StaggerCorePaired33.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at34 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 34 q right rho)
      (atRound s h4 (34+1) (step 34 (message s.memory 34) q) right rho) := by
  exact StaggerCorePaired34.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at35 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 35 q right rho)
      (atRound s h4 (35+1) (step 35 (message s.memory 35) q) right rho) := by
  exact StaggerCorePaired35.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at36 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 36 q right rho)
      (atRound s h4 (36+1) (step 36 (message s.memory 36) q) right rho) := by
  exact StaggerCorePaired36.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at37 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 37 q right rho)
      (atRound s h4 (37+1) (step 37 (message s.memory 37) q) right rho) := by
  exact StaggerCorePaired37.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at38 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 38 q right rho)
      (atRound s h4 (38+1) (step 38 (message s.memory 38) q) right rho) := by
  exact StaggerCorePaired38.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at39 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 39 q right rho)
      (atRound s h4 (39+1) (step 39 (message s.memory 39) q) right rho) := by
  exact StaggerCorePaired39.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at40 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 40 q right rho)
      (atRound s h4 (40+1) (step 40 (message s.memory 40) q) right rho) := by
  exact StaggerCorePaired40.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at41 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 41 q right rho)
      (atRound s h4 (41+1) (step 41 (message s.memory 41) q) right rho) := by
  exact StaggerCorePaired41.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at42 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 42 q right rho)
      (atRound s h4 (42+1) (step 42 (message s.memory 42) q) right rho) := by
  exact StaggerCorePaired42.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at43 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 43 q right rho)
      (atRound s h4 (43+1) (step 43 (message s.memory 43) q) right rho) := by
  exact StaggerCorePaired43.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at44 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 44 q right rho)
      (atRound s h4 (44+1) (step 44 (message s.memory 44) q) right rho) := by
  exact StaggerCorePaired44.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at45 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 45 q right rho)
      (atRound s h4 (45+1) (step 45 (message s.memory 45) q) right rho) := by
  exact StaggerCorePaired45.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at46 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 46 q right rho)
      (atRound s h4 (46+1) (step 46 (message s.memory 46) q) right rho) := by
  exact StaggerCorePaired46.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at47 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 47 q right rho)
      (atRound s h4 (47+1) (step 47 (message s.memory 47) q) right rho) := by
  exact StaggerCorePaired47.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at48 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 48 q right rho)
      (atRound s h4 (48+1) (step 48 (message s.memory 48) q) right rho) := by
  exact StaggerCorePaired48.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at49 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 49 q right rho)
      (atRound s h4 (49+1) (step 49 (message s.memory 49) q) right rho) := by
  exact StaggerCorePaired49.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at50 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 50 q right rho)
      (atRound s h4 (50+1) (step 50 (message s.memory 50) q) right rho) := by
  exact StaggerCorePaired50.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at51 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 51 q right rho)
      (atRound s h4 (51+1) (step 51 (message s.memory 51) q) right rho) := by
  exact StaggerCorePaired51.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at52 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 52 q right rho)
      (atRound s h4 (52+1) (step 52 (message s.memory 52) q) right rho) := by
  exact StaggerCorePaired52.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at53 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 53 q right rho)
      (atRound s h4 (53+1) (step 53 (message s.memory 53) q) right rho) := by
  exact StaggerCorePaired53.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at54 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 54 q right rho)
      (atRound s h4 (54+1) (step 54 (message s.memory 54) q) right rho) := by
  exact StaggerCorePaired54.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at55 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 55 q right rho)
      (atRound s h4 (55+1) (step 55 (message s.memory 55) q) right rho) := by
  exact StaggerCorePaired55.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at56 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 56 q right rho)
      (atRound s h4 (56+1) (step 56 (message s.memory 56) q) right rho) := by
  exact StaggerCorePaired56.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at57 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 57 q right rho)
      (atRound s h4 (57+1) (step 57 (message s.memory 57) q) right rho) := by
  exact StaggerCorePaired57.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at58 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 58 q right rho)
      (atRound s h4 (58+1) (step 58 (message s.memory 58) q) right rho) := by
  exact StaggerCorePaired58.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at59 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 59 q right rho)
      (atRound s h4 (59+1) (step 59 (message s.memory 59) q) right rho) := by
  exact StaggerCorePaired59.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at60 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 60 q right rho)
      (atRound s h4 (60+1) (step 60 (message s.memory 60) q) right rho) := by
  exact StaggerCorePaired60.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at61 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 61 q right rho)
      (atRound s h4 (61+1) (step 61 (message s.memory 61) q) right rho) := by
  exact StaggerCorePaired61.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at62 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 62 q right rho)
      (atRound s h4 (62+1) (step 62 (message s.memory 62) q) right rho) := by
  exact StaggerCorePaired62.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at63 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 63 q right rho)
      (atRound s h4 (63+1) (step 63 (message s.memory 63) q) right rho) := by
  exact StaggerCorePaired63.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at64 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 64 q right rho)
      (atRound s h4 (64+1) (step 64 (message s.memory 64) q) right rho) := by
  exact StaggerCorePaired64.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at65 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 65 q right rho)
      (atRound s h4 (65+1) (step 65 (message s.memory 65) q) right rho) := by
  exact StaggerCorePaired65.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at66 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 66 q right rho)
      (atRound s h4 (66+1) (step 66 (message s.memory 66) q) right rho) := by
  exact StaggerCorePaired66.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at67 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 67 q right rho)
      (atRound s h4 (67+1) (step 67 (message s.memory 67) q) right rho) := by
  exact StaggerCorePaired67.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at68 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 68 q right rho)
      (atRound s h4 (68+1) (step 68 (message s.memory 68) q) right rho) := by
  exact StaggerCorePaired68.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at69 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 69 q right rho)
      (atRound s h4 (69+1) (step 69 (message s.memory 69) q) right rho) := by
  exact StaggerCorePaired69.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at70 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 70 q right rho)
      (atRound s h4 (70+1) (step 70 (message s.memory 70) q) right rho) := by
  exact StaggerCorePaired70.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at71 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 71 q right rho)
      (atRound s h4 (71+1) (step 71 (message s.memory 71) q) right rho) := by
  exact StaggerCorePaired71.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at72 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 72 q right rho)
      (atRound s h4 (72+1) (step 72 (message s.memory 72) q) right rho) := by
  exact StaggerCorePaired72.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at73 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 73 q right rho)
      (atRound s h4 (73+1) (step 73 (message s.memory 73) q) right rho) := by
  exact StaggerCorePaired73.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at74 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 74 q right rho)
      (atRound s h4 (74+1) (step 74 (message s.memory 74) q) right rho) := by
  exact StaggerCorePaired74.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at75 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 75 q right rho)
      (atRound s h4 (75+1) (step 75 (message s.memory 75) q) right rho) := by
  simp only [StaggerModeSeven.step, if_neg (show ¬ StaggerModeSeven.enabled 75 from by decide)]
  exact StaggerCorePaired75.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

private def gasSteps_at76 (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 76 q right rho)
      (atRound s h4 (76+1) (step 76 (message s.memory 76) q) right rho) := by
  simp only [StaggerModeSeven.step, if_neg (show ¬ StaggerModeSeven.enabled 76 from by decide)]
  exact StaggerCorePaired76.gasSteps s h4 q right rho hs hr ha hcode hfork hnp

def gasSteps_step (s : State) (h4 : UInt256) (i : Fin 77) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 i.val q right rho)
      (atRound s h4 (i.val+1) (step i.val (message s.memory i.val) q) right rho) := by
  match i with
  | ⟨0, _⟩ => exact gasSteps_at0 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨1, _⟩ => exact gasSteps_at1 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨2, _⟩ => exact gasSteps_at2 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨3, _⟩ => exact gasSteps_at3 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨4, _⟩ => exact gasSteps_at4 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨5, _⟩ => exact gasSteps_at5 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨6, _⟩ => exact gasSteps_at6 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨7, _⟩ => exact gasSteps_at7 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨8, _⟩ => exact gasSteps_at8 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨9, _⟩ => exact gasSteps_at9 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨10, _⟩ => exact gasSteps_at10 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨11, _⟩ => exact gasSteps_at11 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨12, _⟩ => exact gasSteps_at12 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨13, _⟩ => exact gasSteps_at13 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨14, _⟩ => exact gasSteps_at14 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨15, _⟩ => exact gasSteps_at15 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨16, _⟩ => exact gasSteps_at16 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨17, _⟩ => exact gasSteps_at17 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨18, _⟩ => exact gasSteps_at18 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨19, _⟩ => exact gasSteps_at19 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨20, _⟩ => exact gasSteps_at20 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨21, _⟩ => exact gasSteps_at21 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨22, _⟩ => exact gasSteps_at22 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨23, _⟩ => exact gasSteps_at23 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨24, _⟩ => exact gasSteps_at24 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨25, _⟩ => exact gasSteps_at25 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨26, _⟩ => exact gasSteps_at26 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨27, _⟩ => exact gasSteps_at27 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨28, _⟩ => exact gasSteps_at28 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨29, _⟩ => exact gasSteps_at29 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨30, _⟩ => exact gasSteps_at30 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨31, _⟩ => exact gasSteps_at31 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨32, _⟩ => exact gasSteps_at32 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨33, _⟩ => exact gasSteps_at33 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨34, _⟩ => exact gasSteps_at34 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨35, _⟩ => exact gasSteps_at35 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨36, _⟩ => exact gasSteps_at36 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨37, _⟩ => exact gasSteps_at37 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨38, _⟩ => exact gasSteps_at38 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨39, _⟩ => exact gasSteps_at39 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨40, _⟩ => exact gasSteps_at40 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨41, _⟩ => exact gasSteps_at41 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨42, _⟩ => exact gasSteps_at42 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨43, _⟩ => exact gasSteps_at43 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨44, _⟩ => exact gasSteps_at44 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨45, _⟩ => exact gasSteps_at45 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨46, _⟩ => exact gasSteps_at46 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨47, _⟩ => exact gasSteps_at47 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨48, _⟩ => exact gasSteps_at48 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨49, _⟩ => exact gasSteps_at49 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨50, _⟩ => exact gasSteps_at50 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨51, _⟩ => exact gasSteps_at51 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨52, _⟩ => exact gasSteps_at52 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨53, _⟩ => exact gasSteps_at53 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨54, _⟩ => exact gasSteps_at54 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨55, _⟩ => exact gasSteps_at55 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨56, _⟩ => exact gasSteps_at56 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨57, _⟩ => exact gasSteps_at57 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨58, _⟩ => exact gasSteps_at58 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨59, _⟩ => exact gasSteps_at59 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨60, _⟩ => exact gasSteps_at60 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨61, _⟩ => exact gasSteps_at61 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨62, _⟩ => exact gasSteps_at62 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨63, _⟩ => exact gasSteps_at63 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨64, _⟩ => exact gasSteps_at64 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨65, _⟩ => exact gasSteps_at65 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨66, _⟩ => exact gasSteps_at66 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨67, _⟩ => exact gasSteps_at67 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨68, _⟩ => exact gasSteps_at68 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨69, _⟩ => exact gasSteps_at69 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨70, _⟩ => exact gasSteps_at70 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨71, _⟩ => exact gasSteps_at71 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨72, _⟩ => exact gasSteps_at72 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨73, _⟩ => exact gasSteps_at73 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨74, _⟩ => exact gasSteps_at74 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨75, _⟩ => exact gasSteps_at75 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨76, _⟩ => exact gasSteps_at76 s h4 q right rho hs hr ha hcode hfork hnp
  | ⟨n+77, hi⟩ => exact False.elim (by omega)

def gasSteps_prefix (s : State) (h4 : UInt256) (n : Nat) (hn : n ≤ 77) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 0 q right rho)
      (atRound s h4 n (fold (message s.memory) n q) right rho) := by
  induction n with
  | zero => exact GasSteps.refl _
  | succ n ih =>
    exact (ih (by omega)).trans
      (gasSteps_step s h4 ⟨n, by omega⟩ (fold (message s.memory) n q) right rho hs hr ha hcode hfork hnp)


def suffixState (s : State) (h4 : UInt256) (q : WordLane) (rho : List UInt256) : State :=
  {s with pc := UInt256.ofNat 4689, stack := stack s.memory h4 [ .d, .b, .e, .a, .literal 28, .cachedMessage 360, .k, .c, .er, .cr, .ar, .dr, .br, .factor, .lower, .cache 140, .cache 350, .cache 310, .cache 190, .cache 500 ] (epilogue s.memory q) q (UInt256.ofNat 2840853838) rho}

def gasSteps_suffix (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 77 q right rho) (suffixState s h4 q rho) := by
  have gu := StaggerCoreUnpack.gasSteps s h4 q right rho hs hr ha hcode hfork hnp
  have g1 := StaggerCoreLeft77.gasSteps s h4 (left q) q rho hs hr ha hcode hfork hnp
  have g2 := StaggerCoreLeft78.gasSteps s h4 (left77 s.memory (left q)) q rho hs hr ha hcode hfork hnp
  have g3 := StaggerCoreLeft79.gasSteps s h4 (left78 s.memory (left77 s.memory (left q))) q rho hs hr ha hcode hfork hnp
  exact gu.trans (g1.trans (g2.trans g3))

def gasSteps_pairedSuffix (s : State) (h4 : UInt256) (q right : WordLane) (rho : List UInt256)
    (hs : rho.length ≤ 900) (hr : s.halt = .Running) (ha : 35 ≤ s.activeWords.toNat)
    (hcode : s.executionEnv.code = Artifact.submissionArtifact.code) (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (atRound s h4 0 q right rho)
      (suffixState s h4 (fold (message s.memory) 77 q) rho) :=
  (gasSteps_prefix s h4 77 (by decide) q right rho hs hr ha hcode hfork hnp).trans
    (gasSteps_suffix s h4 (fold (message s.memory) 77 q) right rho hs hr ha hcode hfork hnp)

#print axioms gasSteps_step
#print axioms gasSteps_prefix
#print axioms gasSteps_suffix
#print axioms gasSteps_pairedSuffix
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerCore
