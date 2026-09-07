import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1First
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Second
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Third
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1FourthBody
import Challenge.Modexp.Submission.Proofs.Fast.Cios2L1FourthExit

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast
open Challenge.Modexp.Submission.Proofs.Fast.Monpro
open Challenge.Modexp.Submission.Proofs.Fast.Cios2Paths.L1

/-- Four MACs with one shared loop test. -/
def gasSteps_l1FourBody (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 4 < n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4136 s mem bi pa pb n i j pdst ret rest)
      (l1At 4136 s mem bi pa pb n i (j + 4) pdst ret rest) :=
  (gasSteps_l1FirstMac s mem bi pa pb n i j pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1SecondMac s mem bi pa pb n i (j + 1) pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1ThirdMac s mem bi pa pb n i (j + 2) pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans <|
  gasSteps_l1FourthMacBody s mem bi pa pb n i (j + 3) pdst ret rest hcap hrun
    hcode hfork hnp hact hn32 (by omega) hpa hpaFit

/-- Four MACs with one shared loop test. -/
def gasSteps_l1FourExit (s : State) (mem : ByteArray) (bi : UInt256)
    (pa pb n i j : Nat) (pdst ret : UInt256) (rest : List UInt256)
    (hcap : rest.length ≤ 1008) (hrun : s.halt = .Running)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hact : 296 ≤ s.activeWords.toNat) (hn32 : n ≤ 32) (hj : j + 4 = n)
    (hpa : 32 ≤ pa) (hpaFit : pa + 32 * n ≤ 9472) :
    Challenge.EvmProof.GasSteps
      (l1At 4136 s mem bi pa pb n i j pdst ret rest)
      (midState s (l1Step mem bi pa n (j + 4)).memory
        (UInt256.ofNat (ptrAt (pa + 32 * n - 32) (j + 4)))
        (UInt256.ofNat (ptrAt (8224 + 32 * n) (j + 4)))
        (l1Step mem bi pa n (j + 4)).carry bi pa pb n i pdst ret rest) :=
  (gasSteps_l1FirstMac s mem bi pa pb n i j pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1SecondMac s mem bi pa pb n i (j + 1) pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans <|
  (gasSteps_l1ThirdMac s mem bi pa pb n i (j + 2) pdst ret rest hcap hrun hcode hfork
      hnp hact hn32 (by omega) hpa hpaFit).trans <|
  gasSteps_l1FourthMacExit s mem bi pa pb n i (j + 3) pdst ret rest hcap hrun
    hcode hfork hnp hact hn32 (by omega) hpa hpaFit

end Challenge.Modexp.Submission.Proofs.Fast.Cios2L1Mac
